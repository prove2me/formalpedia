-- Prove2me | Theorems.Thm_TroppMatrixConcentration_trace_cgf_subadditivity
-- name    : TroppMatrixConcentration.trace_cgf_subadditivity
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:44:52.615411+00:00
-- url     : https://prove2.me/theorems/3f65ffb4-87bd-457f-8d1b-a20fc681eeb8
-- title:
--   Lemma 3.5.1 — Subadditivity of matrix cgfs
-- statement:
--   Let $X_1,\ldots,X_N$ be independent measurable Hermitian random $d\times d$ matrices, with $d\ge1$. For any real $\theta$ for which each matrix exponential $e^{\theta X_k}$ is integrable,
--   $$\mathbb E\operatorname{tr}\exp\left(\sum_k\theta X_k\right)\le\operatorname{tr}\exp\left(\sum_k\log\mathbb E e^{\theta X_k}\right).$$
--   The finite-mgf hypothesis makes explicit the source's standing regularity convention. The formula retains the matrix logarithms inside the sum.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 3.5.1, equation (3.5.1), printed pp. 35–36.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem trace_cgf_subadditivity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    (∫ ω, traceExp (∑ k, θ • X k ω) ∂μ) ≤
      traceExp (cumulantSum μ X θ) := by sorry

end TroppMatrixConcentration
