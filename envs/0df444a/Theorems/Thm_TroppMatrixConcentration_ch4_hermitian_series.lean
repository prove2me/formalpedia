-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch4_hermitian_series
-- name    : TroppMatrixConcentration.ch4_hermitian_series
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:46:30.553523+00:00
-- url     : https://prove2.me/theorems/bc880742-d1ff-4985-9328-b3d47a47080c
-- title:
--   Theorem 4.6.1 — Hermitian Gaussian and Rademacher series
-- statement:
--   Let $A_k$ be a finite family of fixed Hermitian complex $d\times d$ matrices, with $d\ge1$. On an arbitrary probability space, let $g_k$ be independent measurable real random variables, either all standard normal or all Rademacher. Put $Y=\sum_k g_k A_k$ and $v=\|\mathbb E Y^2\|$. Then
--   $$v=\left\|\sum_k A_k^2\right\|,\qquad\mathbb E\lambda_{\max}(Y)\le\sqrt{2v\log d},$$
--   $$\mathbb P\{\lambda_{\max}(Y)\ge t\}\le d\exp(-t^2/(2v))\qquad(t\ge0).$$
--   At $v=0$ the tail right side is $d$ for $t=0$ and zero for $t>0$. Empty finite families are allowed. The norm is the Euclidean operator norm; the expectation concerns the largest eigenvalue rather than the norm.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 4.6.1, equations (4.6.1–3), printed p. 51.

import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws
import Definitions.Def_TroppMatrixConcentration_dilation

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch4_hermitian_series {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ k, (A k).IsHermitian)
    (g : Fin N → Ω → ℝ) (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ)
    (hLaw : (∀ k, standardGaussianLaw μ (g k)) ∨ (∀ k, rademacherLaw μ (g k))) :
    let Y := fun ω => ∑ k, g k ω • A k
    let v := hermitianSecondMoment μ Y
    v = spectralNorm (∑ k, A k ^ 2) ∧
    (∫ ω, lambdaMax (Y ω) ∂μ) ≤ Real.sqrt (2 * v * Real.log d) ∧
    ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
      gaussianSeriesTail d v t := by sorry

end TroppMatrixConcentration
