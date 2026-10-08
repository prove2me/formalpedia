-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_laplace_expectations
-- name    : TroppMatrixConcentration.ch3_laplace_expectations
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:44:12.225997+00:00
-- url     : https://prove2.me/theorems/03c714b8-cad4-4e98-b5a7-7dd8467a5e14
-- title:
--   Proposition 3.2.2 — Expectation bounds for eigenvalues
-- statement:
--   For a measurable, Bochner-integrable, almost-surely Hermitian random matrix $Y$ on a probability space, whenever $e^{\theta Y}$ is Bochner integrable,
--   $$\mathbb E\lambda_{\max}(Y)\le\frac{\log\mathbb E\operatorname{tr}e^{\theta Y}}{\theta}\quad(\theta>0),$$
--   $$\mathbb E\lambda_{\min}(Y)\ge\frac{\log\mathbb E\operatorname{tr}e^{\theta Y}}{\theta}\quad(\theta<0).$$
--   The integrability hypotheses make the expectations finite. The pointwise parameter formulation supports the source's infimum and supremum optimizations over admissible parameters.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 3.2.2, printed p. 33.

import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch3_laplace_expectations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : Measurable Y) (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hInt : Integrable Y μ)
    (hExp : Integrable (fun ω => matrixExp (θ • Y ω)) μ) :
    (0 < θ → (∫ ω, lambdaMax (Y ω) ∂μ) ≤
      Real.log (∫ ω, traceExp (θ • Y ω) ∂μ) / θ) ∧
    (θ < 0 → Real.log (∫ ω, traceExp (θ • Y ω) ∂μ) / θ ≤
      (∫ ω, lambdaMin (Y ω) ∂μ)) := by sorry

end TroppMatrixConcentration
