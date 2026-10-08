-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_expect_extrema_integrable
-- name    : TroppMatrixConcentration.ch3_expect_extrema_integrable
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:08:28.772431+00:00
-- url     : https://prove2.me/theorems/adadf8ad-aeab-41fd-b0d0-d2f0f8d067a0
-- title:
--   Integrability of extreme eigenvalues
-- statement:
--   Let $Y$ be a measurable, almost surely Hermitian complex $d\times d$ random matrix, $d\ge1$, on any measure space. If $Y$ is Bochner integrable in the Euclidean operator norm, then
--
--   $$\lambda_{\max}(Y),\ \lambda_{\min}(Y)\in L^1.$$
--
--   No finite-measure or probability assumption is needed. This supporting regularity lemma makes the expectations in the matrix Laplace method well-defined.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Auxiliary regularity lemma for Proposition 3.2.2, printed p. 33; uses spectral norm relation (2.1.22), printed p. 24, and the standing regularity convention of Section 2.2.1, printed p. 25.

import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

/-- The extreme eigenvalues of an integrable Hermitian random matrix are integrable. -/
theorem ch3_expect_extrema_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : Measurable Y) (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hInt : Integrable Y μ) :
    Integrable (fun ω => lambdaMax (Y ω)) μ ∧
    Integrable (fun ω => lambdaMin (Y ω)) μ := by sorry

end TroppMatrixConcentration
