-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_localizable_products
-- name    : QAlgorithms.Papers.Independent.Support21.P20.localizable_products
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:56:53.060388+00:00
-- url     : https://prove2.me/theorems/b838dc5c-c47c-43d5-9c95-6265e44cb7c5
-- title:
--   Small products of localizable Boolean algebras
-- statement:
--   Let $(A_i)_{i\in I}$ be any small family of localizable complete Boolean algebras. Form $P=\prod_{i\in I}A_i$ with coordinatewise order and Boolean operations, and let $\pi_i:P\to A_i$ be evaluation at $i$. Then
--
--   $$P\text{ is localizable},\qquad (P,(\pi_i))\text{ is a product in both }\mathbf{LBAlg}\text{ and }\mathbf{BAlg}.$$
--
--   More explicitly, each projection preserves arbitrary suprema. Every family of complete unital Boolean homomorphisms from a localizable Boolean algebra $B$ has a unique complete homomorphism $g:B\to P$ with $\pi_i g=f_i$. For an arbitrary Boolean algebra $B$ and unital Boolean homomorphisms $f_i$, there is likewise a unique unital Boolean homomorphism with those coordinates. These are the two universal properties expressing preservation by the forgetful functor. The empty product is the one-element algebra. No direct-sum identification is asserted.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 17, Proposition 2.54

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Proposition 2.54, PDF p.17: small products and their preservation by forgetting
completeness/localizability, expanded as the universal properties of the same
coordinate projections. The empty product is included. -/
theorem localizable_products (I : Type u) (A : I → Type u)
    [∀ i, CompleteBooleanAlgebra (A i)] (hA : ∀ i, HasFiniteValuationCover (A i)) :
    HasFiniteValuationCover ((i : I) → A i) ∧
    (∀ i : I, PreservesSuprema (fun a : ((i : I) → A i) => a i)) ∧
    (∀ (B : Type u) [CompleteBooleanAlgebra B], HasFiniteValuationCover B →
      ∀ f : (i : I) → BoundedLatticeHom B (A i),
        (∀ i, PreservesSuprema (f i)) →
        ∃! g : BoundedLatticeHom B ((i : I) → A i),
          PreservesSuprema g ∧ ∀ i b, g b i = f i b) ∧
    (∀ (B : Type u) [BooleanAlgebra B] (f : (i : I) → BoundedLatticeHom B (A i)),
      ∃! g : BoundedLatticeHom B ((i : I) → A i), ∀ i b, g b i = f i b) := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
