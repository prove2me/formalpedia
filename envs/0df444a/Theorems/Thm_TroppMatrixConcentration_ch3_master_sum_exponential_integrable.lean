-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_master_sum_exponential_integrable
-- name    : TroppMatrixConcentration.ch3_master_sum_exponential_integrable
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:08:28.625929+00:00
-- url     : https://prove2.me/theorems/a99856cf-d66e-4e85-b20e-2b7c7b4e4212
-- title:
--   Exponential integrability of an independent Hermitian sum
-- statement:
--   On any probability space, let $X_k$ be a finite independent family of measurable, almost surely Hermitian complex $d\times d$ matrices, with $d\ge1$. Fix $\theta\in\mathbb R$. If every $e^{\theta X_k}$ is Bochner integrable, then
--
--   $$\exp\!\left(\theta\sum_k X_k\right)\in L^1.$$
--
--   The family may be empty and the parameter may be zero. No integrability of the summands themselves is assumed. This auxiliary lemma supplies the exponential integrability needed to apply Laplace bounds to independent sums.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Auxiliary regularity lemma for the proof of Theorem 3.6.1, printed p. 36; Section 2.2.1, printed p. 25, states the standing regularity convention. This is explicit analytic groundwork, not a separately numbered theorem in the book.

import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

namespace TroppMatrixConcentration

/-- Exponential integrability passes from independent Hermitian summands to their sum. -/
theorem ch3_master_sum_exponential_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    Integrable (fun ω => matrixExp (θ • ∑ k, X k ω)) μ := by sorry

end TroppMatrixConcentration
