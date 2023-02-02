{-# OPTIONS --safe #-}
module ScopeGraph.Graph where

open import Function.Base using (const; _∘_; flip)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
open import Level using (Level)
open import Data.Product using (∃; ∃₂; -,_; _×_; _,_; proj₁; proj₂; Σ; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; icong)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; fold)
open import Relation.Nullary using (Dec; no; yes)

open import KL.Prelude
open Levels
open import KL.DecEq
open DecEq ⦃ ... ⦄
open import Finite
open IsFinite

instance
  Star-DecEq :
    {A : Set ℓ}
    {R : A → A → Set ℓ′}
    ⦃ _ : DecEq A ⦄ ⦃ _ : {a b : A} → DecEq (R a b) ⦄
    {a b : A} → DecEq (Star R a b)
  (Star-DecEq DecEq.≟ ε) ε = yes refl
  (Star-DecEq DecEq.≟ ε) (_ ◅ _) = no λ ()
  (Star-DecEq DecEq.≟ (_ ◅ _)) ε = no λ ()
  (Star-DecEq DecEq.≟ (_◅_ {j = i} d p)) (_◅_ {j = j} e q) with i ≟ j
  ... | no ¬w = no λ where refl → ¬w refl
  ... | yes refl with d ≟ e | p ≟ q
  ... | no ¬w    | _        = no λ where refl → ¬w refl
  ... | _        | no ¬w    = no λ where refl → ¬w refl
  ... | yes refl | yes refl = yes refl

private
  variable
    A : Set ℓ
    a b c : A
    m n : ℕ

module Path {A : Type ℓ} (R : A → A → Type ℓ′) where

  data Path (a : A) : A → ℕ → Type (ℓ ⊔ ℓ′) where
    ε   :                      Path a a 0
    _◅_ : R a b → Path b c n → Path a c (suc n)

  infixr 5 _▻_
  infixl 5 _◅◅_
  _◅◅_   : Path a b m → Path b c n → Path a c (m + n)
  _▻_    : Path a b n → R b c → Path a c (suc n)
  unsnoc : (p : Path a c (suc n)) → ∃ λ b → ∃₂ λ (p′ : Path a b n) (e : R b c) → p ≡ p′ ▻ e

  ε ◅◅ q = q
  (e ◅ p) ◅◅ q = e ◅ (p ◅◅ q)

  ε ▻ e = e ◅ ε
  (e ◅ p) ▻ e′ = e ◅ p ▻ e′

  unsnoc (e ◅ ε) = -, ε , e , refl
  unsnoc (e ◅ d ◅ p) with unsnoc (d ◅ p)
  … | b , p′ , e′ , eq rewrite eq = b , e ◅ p′ , e′ , refl

  Path< Path≤ : A → A → ℕ → Type _
  Path< a b n = ∃ λ m → m < n × Path a b m
  Path≤ a b n = ∃ λ m → m ≤ n × Path a b m

  boundedPath : {P : ℕ → Type} (p : ∃ λ n → P n × Path a b n) → Path a b (proj₁ p)
  boundedPath = proj₂ ∘ proj₂

module _ {A : Set ℓ} {R : A → A → Set ℓ′} where
  open Path R

  starLength : Star R a b → ℕ
  starLength = fold _ (const suc) 0

  toStar : Path a b n → Star R a b
  toStar ε       = ε
  toStar (e ◅ p) = e ◅ toStar p

  fromStar : (p : Star R a b) → Path a b (starLength p)
  fromStar ε       = ε
  fromStar (e ◅ p) = e ◅ fromStar p

  toStar-fromStar : (p : Star R a b) → p ≡ toStar (fromStar p)
  toStar-fromStar ε       = refl
  toStar-fromStar (e ◅ p) = cong (e ◅_) (toStar-fromStar p)

  starLength-toStar : (p : Path a b n) → n ≡ starLength (toStar p)
  starLength-toStar ε       = refl
  starLength-toStar (e ◅ p) = cong suc (starLength-toStar p)

  fromStar-toStar′ : (p : Path a b n) →
                     _≡_ {A = Σ _ (Path a b)} (n , p) (starLength (toStar p) , fromStar (toStar p))
  fromStar-toStar′ ε       = refl
  fromStar-toStar′ (e ◅ p) = cong (map suc (e ◅_)) (fromStar-toStar′ p)

record FiniteGraph ℓ ℓ′ : Type (lsuc (ℓ ⊔ ℓ′)) where
  constructor finiteGraph
  field    
    {Vertex} : Type ℓ
    {Edge}   : Vertex → Vertex → Type ℓ′
    Vertexᶠ  : IsFinite Vertex
    Edgeᶠ    : IsFinite (∃₂ Edge)

  instance
    decEq-vertex : DecEq Vertex
    decEq-vertex = finite-decEq Vertexᶠ

  edgeFromᶠ : (v : Vertex) → IsFinite (∃ (Edge v))
  edgeFromᶠ v = ?
    -- filterPropᶠ (λ where (a′ , _ , _) → a ≟ a′) Edgeᶠ <&ᶠ>
    --   surjection
    --     (λ where ((_ , _ , e) , refl) → -, e)
    --     (λ where (_ , e) → (-, -, e) , refl)
    --     (λ where (_ , e) → refl)

  edgeToᶠ : (v₂ : Vertex) → IsFinite (∃ λ v₁ → Edge v₁ v₂)
  edgeToᶠ v₂ = {!!}
    -- filterPropᶠ (λ where (_ , b′ , _) → b ≟ b′) Edgeᶠ <&ᶠ>
    --   surjection
    --     (λ where ((_ , _ , e) , refl) → -, e)
    --     (λ where (_ , e) → (-, -, e) , refl)
    --     (λ where (_ , e) → refl)
