-- Prove2me | Theorems.Thm_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension
-- name    : TwoChartCech.finrank_ker_baseChange_eq_of_field_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/4e8652e5-eabf-5790-8b66-983e5f9e1739
-- title:
--   Invariance of dimker(d⊗ K) under field extension
-- statement:
--   Fix a commutative ring $R$ and two $R$-modules $C^0$, $C^1$ (given as additive commutative groups with $R$-module structures), all in a single universe, together with an $R$-linear map $d \colon C^0 \to C^1$. Let $K$ and $L$ be fields, each equipped with an $R$-algebra structure, let $L$ be a $K$-algebra, and assume the scalar-tower compatibility between the actions of $R$, $K$ and $L$, so that $R \to K \to L$ commutes with $R \to L$. No flatness, finiteness or finite-dimensionality hypotheses are imposed on $C^0$, $C^1$ or on the extension. The conclusion is an equality of natural numbers: the $K$-dimension of the kernel of the base-changed map $d \otimes_R K \colon K \otimes_R C^0 \to K \otimes_R C^1$ equals the $L$-dimension of the kernel of $d \otimes_R L \colon L \otimes_R C^0 \to L \otimes_R C^1$. Since the dimensions are measured by `Module.finrank`, which is $0$ on modules that are not finite-dimensional, the statement in particular asserts that one kernel is finite-dimensional exactly when the other is (both being of the same positive dimension), or else that both sides are $0$.
--
--   This is the flat base change statement that $h^0$ of a two-term complex is unchanged when the field of coefficients is enlarged: kernels commute with the base change $K \to L$ and dimension is preserved by $L \otimes_K -$. It is used to compare fibre ranks of a two-chart Čech complex computed over different residue fields of a base, and to pass to geometric fibres; it is invoked in the relative Picard and two-affine-open-cover rank comparisons [`AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq`](thm.html#AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq), [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff) and [`TwoChartCech.exists_fibreH0Family`](thm.html#TwoChartCech.exists_fibreH0Family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct

theorem TwoChartCech.finrank_ker_baseChange_eq_of_field_extension
    {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) (K L : Type u) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank L (LinearMap.ker (d.baseChange L)) := by sorry
