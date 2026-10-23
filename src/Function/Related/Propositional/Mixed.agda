------------------------------------------------------------------------
-- The Agda standard library
--
-- Relatedness for the function hierarchy
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Related.Propositional.Mixed where

open import Level using (Level; 0ℓ; _⊔_)
open import Function.Base using (id; _∘_; _∘′_; _∘₂_; const; flip)
open import Function.Definitions using (Inverseᵇ; Inverseˡ; Inverseʳ; Injective)
open import Function.Bundles using
  ( _⟶_; _↣_; _⇔_; _↪_; _↔_
  ; mk⟶; mk↣; mk⇔; mk↪; mk↔
  ; Func; Injection; Equivalence; RightInverse; Inverse
  )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Bool using (T)
open import Data.Maybe as Maybe using (Maybe; nothing; just; is-just)
open import Data.Maybe.Relation.Unary.All as All using (All; nothing; just)
open import Data.Maybe.Relation.Binary.Connected as Connected
  using (Connected; nothing; just; nothing-just; just-nothing)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.Reasoning.Syntax hiding (forward; backward)
open import Function.Consequences using (inverseʳ⇒injective)
open import Function.Properties.RightInverse using (↪⇒↠)
open import Function.Properties.Inverse using (↔-refl)
open import Function.Properties.Bijection using (⤖⇒↔)
open import Function.Properties.Surjection using (↠⇒↪)

open import Function.Related.Propositional

import Data.Maybe.Relation.Unary.All.Properties as All
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a b c : Level
    A B C : Set a
    k k′ : Kind

record MixedRelated (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor related
  field mto : Maybe (A → B)
        mfrom : Maybe (B → A)
        mto-inj : All (Maybe ∘ Injective _≡_ _≡_) mto
        mfrom-inj : All (Maybe ∘ Injective _≡_ _≡_) mfrom
        minverseˡ : Connected (Maybe ∘₂ Inverseˡ _≡_ _≡_) mto mfrom
        minverseʳ : Connected (Maybe ∘₂ Inverseʳ _≡_ _≡_) mto mfrom

open MixedRelated

unrelated : MixedRelated A B
unrelated = record
  { mto = nothing
  ; mfrom = nothing
  ; mto-inj = nothing
  ; mfrom-inj = nothing
  ; minverseˡ = nothing
  ; minverseʳ = nothing
  }

mkForward : (to : A → B) → Maybe (Injective _≡_ _≡_ to) → MixedRelated A B
mkForward to inj = record
  { mto = just to
  ; mfrom = nothing
  ; mto-inj = just inj
  ; mfrom-inj = nothing
  ; minverseˡ = just-nothing
  ; minverseʳ = just-nothing
  }

mkBackward : (from : B → A) → Maybe (Injective _≡_ _≡_ from) → MixedRelated A B
mkBackward from inj = record
  { mto = nothing
  ; mfrom = just from
  ; mto-inj = nothing
  ; mfrom-inj = just inj
  ; minverseˡ = nothing-just
  ; minverseʳ = nothing-just
  }

mkEquiv : (to : A → B) (from : B → A)
  → Maybe (Inverseˡ _≡_ _≡_ to from)
  → Maybe (Inverseʳ _≡_ _≡_ to from)
  → MixedRelated A B
mkEquiv to from invˡ invʳ = record
  { mto = just to
  ; mfrom = just from
  ; mto-inj = just (Maybe.map (inverseʳ⇒injective _≡_ to ≡.refl ≡.sym ≡.trans) invʳ)
  ; mfrom-inj = just (Maybe.map (inverseʳ⇒injective _≡_ from ≡.refl ≡.sym ≡.trans) invˡ)
  ; minverseˡ = just invˡ
  ; minverseʳ = just invʳ
  }

encode : Related k A B → MixedRelated A B
encode {k = implication}         f = mkForward to nothing where open Func f
encode {k = reverseImplication}  f = mkBackward to nothing where open Func f
encode {k = equivalence}         f = mkEquiv to from nothing nothing where open Equivalence f
encode {k = injection}           f = mkForward to (just injective) where open Injection f
encode {k = reverseInjection}    f = mkBackward to (just injective) where open Injection f
encode {k = leftInverse}         f = mkEquiv to from nothing (just inverseʳ) where open RightInverse f
encode {k = surjection}          f = mkEquiv from to (just inverseʳ) nothing where open RightInverse (↠⇒↪ f)
encode {k = bijection}           f = mkEquiv to from (just inverseˡ) (just inverseʳ) where open Inverse f

pattern forward to to-inj = record
  { mto = just to
  ; mto-inj = just to-inj
  }

pattern backward from from-inj = record
  { mfrom = just from
  ; mfrom-inj = just from-inj
  }

pattern equiv to from invˡ invʳ = record
  { mto = just to
  ; mfrom = just from
  ; minverseˡ = just invˡ
  ; minverseʳ = just invʳ
  }

decode : MixedRelated A B → Maybe (Related k A B)
decode {k = implication}        (forward to _)                      = just (mk⟶ to)
decode {k = reverseImplication} (backward from _)                   = just (mk⟶ from)
decode {k = injection}          (forward _ (just inj))              = just (mk↣ inj)
decode {k = reverseInjection}   (backward _ (just inj))             = just (mk↣ inj)
decode {k = equivalence}        (equiv to from _ _)                 = just (mk⇔ to from)
decode {k = leftInverse}        (equiv _ _ _ (just invʳ))           = just (mk↪ invʳ)
decode {k = surjection}         (equiv _ _ (just invˡ) _)           = just (↪⇒↠ (mk↪ invˡ))
decode {k = bijection}          (equiv _ _ (just invˡ) (just invʳ)) = just (mk↔ (invˡ , invʳ))
{-# CATCHALL #-}
decode _ = nothing

HasKind : (k : Kind) (r : MixedRelated A B) → Set _
HasKind k r = T (is-just (decode {k = k} r))

MK-refl : MixedRelated A A
MK-refl = encode ↔-refl

MK-reflexive : A ≡ B → MixedRelated A B
MK-reflexive ≡.refl = MK-refl

MK-sym : MixedRelated A B → MixedRelated B A
MK-sym f .mto = f .mfrom
MK-sym f .mfrom = f .mto
MK-sym f .mto-inj = f .mfrom-inj
MK-sym f .mfrom-inj = f .mto-inj
MK-sym f .minverseˡ = Connected.sym id (f .minverseʳ)
MK-sym f .minverseʳ = Connected.sym id (f .minverseˡ)

MK-trans : MixedRelated A B → MixedRelated B C → MixedRelated A C
MK-trans f g .mto = Maybe.zipWith (flip _∘′_) (f .mto) (g .mto)
MK-trans f g .mfrom = Maybe.zipWith _∘′_ (f .mfrom) (g .mfrom)
MK-trans f g .mto-inj = All.zipWith⁺ (Maybe.zipWith (Composition.injective _≡_ _≡_ _≡_)) (f .mto-inj) (g .mto-inj)
MK-trans f g .mfrom-inj = All.zipWith⁺ (Maybe.zipWith (flip (Composition.injective _≡_ _≡_ _≡_))) (f .mfrom-inj) (g .mfrom-inj)
MK-trans f g .minverseˡ = Connected.zipWith⁺ (Maybe.zipWith (flip (Composition.inverseʳ _≡_ _≡_ _≡_))) (f .minverseˡ) (g .minverseˡ)
MK-trans f g .minverseʳ = Connected.zipWith⁺ (Maybe.zipWith (Composition.inverseʳ _≡_ _≡_ _≡_)) (f .minverseʳ) (g .minverseʳ)

------------------------------------------------------------------------
-- Equational reasoning

-- Equational reasoning for related things. Note that we don't use
-- the `Relation.Binary.Reasoning.Syntax` for this as this relation
-- is heterogeneous.

module Reasoning where

  -- special begin syntax

  extract : (mr : MixedRelated A B) → {w : HasKind k mr} → Related k A B
  extract {k = k} mr with just r ← decode {k = k} mr = r

  infix 1 begin_ extract
  begin_ = extract

  syntax extract {k = k} mr = begin[ k ] mr

  -- Combinators with one heterogeneous relation
  module _ {a b : Level} where
    open ≡-syntax (MixedRelated {a} {b}) (MK-trans ∘′ MK-reflexive) public

  -- Combinators with two heterogeneous relations
  module _ {a b c : Level} where
    private
      rel1 = MixedRelated {b} {c}
      rel2 = MixedRelated {a} {c}

    open ∼-syntax rel1 rel2 MK-trans public
    open ⤖-syntax rel1 rel2 (MK-trans ∘′ encode ∘′ ⤖⇒↔) Symmetry.⤖-sym public
    open ↔-syntax rel1 rel2 (MK-trans ∘′ encode) Symmetry.↔-sym public
    open ⟶-syntax rel1 rel2 (MK-trans ∘′ encode {k = implication}) public

    private
      step : (A : Set a) {B : Set b} {C : Set c} → Related k B C → MixedRelated A B → MixedRelated A C
      step x y∼z x∼y = MK-trans x∼y (encode y∼z)

    infixr 2 step-⟵ step-↣ step-↢ step-↠ step-↪ step-↞ step-↩ step-⇔

    step-⟵ = step {k = reverseImplication}
    step-↣ = step {k = injection}
    step-↢ = step {k = reverseInjection}
    step-↠ = step {k = surjection}
    step-↪ = step {k = leftInverse}
    step-↞ = step {k = leftInverse}
    step-↩ = step {k = surjection}
    step-⇔ = step {k = equivalence}

    syntax step-⟵ x y∼z x∼y = x ⟵⟨ x∼y ⟩ y∼z
    syntax step-↣ x y∼z x∼y = x ↣⟨ x∼y ⟩ y∼z
    syntax step-↢ x y∼z x∼y = x ↢⟨ x∼y ⟩ y∼z
    syntax step-↠ x y∼z x∼y = x ↠⟨ x∼y ⟩ y∼z
    syntax step-↪ x y∼z x∼y = x ↪⟨ x∼y ⟩ y∼z
    syntax step-↞ x y∼z x∼y = x ↞⟨ x∼y ⟩ y∼z
    syntax step-↩ x y∼z x∼y = x ↩⟨ x∼y ⟩ y∼z
    syntax step-⇔ x y∼z x∼y = x ⇔⟨ x∼y ⟩ y∼z

  -- Combinators with homogeneous relations
  module _ {a : Level} where
    open end-syntax (MixedRelated {a}) MK-refl public
