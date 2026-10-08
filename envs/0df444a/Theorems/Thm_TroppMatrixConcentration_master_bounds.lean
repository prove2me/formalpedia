-- Prove2me | Theorems.Thm_TroppMatrixConcentration_master_bounds
-- name    : TroppMatrixConcentration.master_bounds
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:45:30.557721+00:00
-- url     : https://prove2.me/theorems/c3d89af4-5c89-456d-941a-35f9b5cf677e
-- title:
--   Theorem 3.6.1 — Master expectation and tail bounds
-- statement:
--   Let $X_k$ be a finite independent family of measurable integrable Hermitian random $d\times d$ matrices on a probability space, with $d\ge1$. Fix a real parameter $\theta$ such that every $e^{\theta X_k}$ is integrable. Set $Y=\sum_kX_k$ and $K(\theta)=\sum_k\log\mathbb E e^{\theta X_k}$. If $\theta>0$, then
--   $$\mathbb E\lambda_{\max}(Y)\le\frac{\log\operatorname{tr}e^{K(\theta)}}\theta,\qquad\mathbb P\{\lambda_{\max}(Y)\ge t\}\le e^{-\theta t}\operatorname{tr}e^{K(\theta)}.$$
--   If $\theta<0$, then
--   $$\mathbb E\lambda_{\min}(Y)\ge\frac{\log\operatorname{tr}e^{K(\theta)}}\theta,\qquad\mathbb P\{\lambda_{\min}(Y)\le t\}\le e^{-\theta t}\operatorname{tr}e^{K(\theta)}.$$
--   Both tail bounds hold for every real $t$. These are the pointwise-parameter forms of all four master bounds; optimization over admissible parameters gives the source's infima and supremum. The case $\theta=0$ imposes no conclusion.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 3.6.1, equations (3.6.1–4), printed pp. 36.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem master_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hInt : ∀ k, Integrable (X k) μ) (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    (0 < θ →
      (∫ ω, lambdaMax (∑ k, X k ω) ∂μ) ≤
        Real.log (traceExp (cumulantSum μ X θ)) / θ ∧
      ∀ t : ℝ, (μ {ω | t ≤ lambdaMax (∑ k, X k ω)}).toReal ≤
        Real.exp (-θ * t) * traceExp (cumulantSum μ X θ)) ∧
    (θ < 0 →
      Real.log (traceExp (cumulantSum μ X θ)) / θ ≤
        (∫ ω, lambdaMin (∑ k, X k ω) ∂μ) ∧
      ∀ t : ℝ, (μ {ω | lambdaMin (∑ k, X k ω) ≤ t}).toReal ≤
        Real.exp (-θ * t) * traceExp (cumulantSum μ X θ)) := by sorry

end TroppMatrixConcentration
