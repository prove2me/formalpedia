-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch7_intrinsic_dimension
-- name    : TroppMatrixConcentration.ch7_intrinsic_dimension
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:51:46.808236+00:00
-- url     : https://prove2.me/theorems/6c5757aa-9d24-4c77-bfe9-b3af20de5f9e
-- title:
--   Lemma 7.5.1 — Intrinsic dimension trace inequality
-- statement:
--   For every real function $\varphi$ convex on $[0,\infty)$ with $\varphi(0)=0$, and every positive semidefinite complex $d\times d$ matrix $A$, $d\ge1$,
--   $$\operatorname{tr}\varphi(A)\le r(A)\varphi(\|A\|).$$
--   The function of the matrix is defined by spectral functional calculus. Zero matrices are included using the totalized convention $r(0)=0$, so both sides are zero. No nonnegativity assumption on $\varphi$ is imposed.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 7.5.1, printed pp. 112–113.

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch7_intrinsic_dimension {d : ℕ} [NeZero d]
    (φ : ℝ → ℝ) (hConvex : ConvexOn ℝ (Set.Ici 0) φ) (hZero : φ 0 = 0)
    (A : Matrix (Fin d) (Fin d) ℂ) (hPSD : A.PosSemidef) :
    traceFunction φ A ≤ intrinsicDimension A * φ (spectralNorm A) := by sorry

end TroppMatrixConcentration
