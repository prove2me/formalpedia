-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P67_generalLinear_universalFormSpace
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P67.generalLinear_universalFormSpace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:25:03.916976+00:00
-- url     : https://prove2.me/theorems/d359231f-8be9-4919-bb9c-e2e9a7a9c0fa
-- title:
--   The universal coefficient space of the general linear Lie algebra
-- statement:
--   For an integer $n\ge2$, let $\mathfrak{gl}_n(\mathbb R)$ be the real matrix Lie algebra, $\mathfrak{sl}_n(\mathbb R)$ its trace-zero subalgebra, and $\mathbb R$ the one-dimensional abelian Lie algebra. Then
--
--   $$V(\mathfrak{gl}_n(\mathbb R))\cong V(\mathfrak{sl}_n(\mathbb R))\oplus V(\mathbb R)\cong\mathbb R^2.$$
--
--   This is a concrete instance of the universal coefficient decomposition. The range $n\ge2$ is implicit in the source's assertion that $\mathfrak{sl}_n$ is central simple. At $n=1$ the coefficient space has dimension one.
-- source:
--   Central extensions of groups of sections, arXiv:0711.3437v2, PDF p. 42, Example B.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P67

namespace QAlgorithms.Papers.Independent.Intakenext100.P67

open scoped TensorProduct

universe u v w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieRing

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieAlgebra

section MatrixExample

attribute [local instance] LieRing.ofAssociativeRing

/-- Example B.5, PDF p. 42: for n ≥ 2 the universal coefficient space of
gl_n(R) splits into those of sl_n(R) and the one-dimensional abelian algebra,
and this direct sum is R². The source's assertion that sl_n is central simple
implicitly requires n ≥ 2; n = 0 and n = 1 are not included. -/
theorem generalLinear_universalFormSpace (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (UniversalFormSpace (Matrix (Fin n) (Fin n) ℝ) ≃ₗ[ℝ]
      (UniversalFormSpace (LieAlgebra.SpecialLinear.sl (Fin n) ℝ) ×
        UniversalFormSpace ℝ)) ∧
    Nonempty ((UniversalFormSpace (LieAlgebra.SpecialLinear.sl (Fin n) ℝ) ×
        UniversalFormSpace ℝ) ≃ₗ[ℝ] (ℝ × ℝ)) := by sorry

end MatrixExample

end QAlgorithms.Papers.Independent.Intakenext100.P67
