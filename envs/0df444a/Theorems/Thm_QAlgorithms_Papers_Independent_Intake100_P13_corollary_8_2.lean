-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P13_corollary_8_2
-- name    : QAlgorithms.Papers.Independent.Intake100.P13.corollary_8_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:11:46.895347+00:00
-- url     : https://prove2.me/theorems/904dec3a-af4d-4c9d-917d-8b1e8033708e
-- title:
--   Corollary 8.2
-- statement:
--   Let $A$ and $B$ be complex C*-algebras, possibly nonunital or zero, and let $M(B)$ be the double-centralizer multiplier algebra of $B$. Let $\pi:A\to M(B)$ be a complex-linear star homomorphism. Suppose the complex linear span of the products $\pi(a)b$, with $a\in A$ and $b\in B$, is norm dense in $B$. Then
--   $$
--   \forall y\in B\quad \exists a\in A\ \exists b\in B:\quad y=\pi(a)b.
--   $$
--   This factorization gives a single product for each element, rather than just approximation by finite sums.
-- source:
--   A complex semigroup approach to group algebras of infinite dimensional Lie groups, arXiv:0709.1062v1, PDF p. 38, Corollary 8.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P13

namespace QAlgorithms.Papers.Independent.Intake100.P13

open Set Filter Topology

noncomputable section

universe u v w

section Multipliers

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A}

/-- Corollary 8.2, PDF p. 38: every element is one product. The dense
span hypothesis is the source's nondegenerate multiplier action; no unit
or nonzero algebra is required. -/
theorem corollary_8_2
    {B : Type v} [NonUnitalCStarAlgebra B]
    (pi : A →⋆ₙₐ[ℂ] DoubleCentralizer ℂ B)
    (hDense : Dense (Submodule.span ℂ
      {y : B | ∃ a : A, ∃ b : B, (pi a).fst b = y} : Set B)) :
    ∀ y : B, ∃ a : A, ∃ b : B, y = (pi a).fst b := by sorry

end Multipliers

end

end QAlgorithms.Papers.Independent.Intake100.P13
