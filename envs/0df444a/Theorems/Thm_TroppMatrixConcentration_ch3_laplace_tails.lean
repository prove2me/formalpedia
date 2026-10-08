-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_laplace_tails
-- name    : TroppMatrixConcentration.ch3_laplace_tails
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:43:49.425176+00:00
-- url     : https://prove2.me/theorems/08e592b5-3405-415b-98ef-3876e3fc6d44
-- title:
--   Proposition 3.2.1 — Tail bounds for eigenvalues
-- statement:
--   For a measurable, almost-surely Hermitian random matrix $Y$ on a probability space, whenever $e^{\theta Y}$ is Bochner integrable,
--   $$\mathbb P\{\lambda_{\max}(Y)\ge t\}\le e^{-\theta t}\mathbb E\operatorname{tr}e^{\theta Y}\quad(\theta>0),$$
--   $$\mathbb P\{\lambda_{\min}(Y)\le t\}\le e^{-\theta t}\mathbb E\operatorname{tr}e^{\theta Y}\quad(\theta<0).$$
--   Both bounds hold for every real threshold $t$. These pointwise parameter bounds provide the source's infimum bounds over parameters with finite matrix mgf.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 3.2.1, printed pp. 32–33.

import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch3_laplace_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : Measurable Y) (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (θ • Y ω)) μ) :
    (0 < θ → ∀ t : ℝ,
      (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
        Real.exp (-θ * t) * (∫ ω, traceExp (θ • Y ω) ∂μ)) ∧
    (θ < 0 → ∀ t : ℝ,
      (μ {ω | lambdaMin (Y ω) ≤ t}).toReal ≤
        Real.exp (-θ * t) * (∫ ω, traceExp (θ • Y ω) ∂μ)) := by sorry

end TroppMatrixConcentration
