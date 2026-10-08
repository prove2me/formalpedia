-- Prove2me | Theorems.Thm_TroppMatrixConcentration_matrix_bernstein
-- name    : TroppMatrixConcentration.matrix_bernstein
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:52:16.236065+00:00
-- url     : https://prove2.me/theorems/25e4ce67-33ae-48fd-9e24-bce932a53511
-- title:
--   Theorem 6.1.1 — Matrix Bernstein for rectangular matrices
-- statement:
--   Let $S_1,\ldots,S_N$ be independent measurable complex $m\times n$ random matrices on a probability space, with $m,n\ge1$. Assume $\mathbb ES_k=0$ and $\|S_k\|\le L$ almost surely, where $L\ge0$ and the norm is the spectral norm. Set $Z=\sum_kS_k$. Then
--   $$v=\max\{\|\mathbb EZZ^*\|,\|\mathbb EZ^*Z\|\}=\max\left\{\left\|\sum_k\mathbb ES_kS_k^*\right\|,\left\|\sum_k\mathbb ES_k^*S_k\right\|\right\},$$
--   $$\mathbb E\|Z\|\le\sqrt{2v\log(m+n)}+\frac L3\log(m+n),$$
--   $$\mathbb P\{\|Z\|\ge t\}\le(m+n)\exp\left(-\frac{t^2/2}{v+Lt/3}\right)\quad(t\ge0).$$
--   At a zero denominator the tail right-hand side is $m+n$ for $t=0$ and zero for $t>0$. The finite family may be empty. All moments needed in this statement exist by boundedness. This is the mission's goal, retaining both the expectation and tail conclusions.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 6.1.1, equations (6.1.1–4), printed pp. 76.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem matrix_bernstein {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n N : ℕ} [NeZero m] [NeZero n]
    (S : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (S k)) (hIndep : iIndepFun S μ)
    (hMean : ∀ k, (∫ ω, S k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, spectralNorm (S k ω) ≤ L) :
    let Z := fun ω => ∑ k, S k ω
    let v := rectSecondMoment μ Z
    v = max (spectralNorm (∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ))
      (spectralNorm (∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ)) ∧
    (∫ ω, spectralNorm (Z ω) ∂μ) ≤
      Real.sqrt (2 * v * Real.log (m + n)) + L * Real.log (m + n) / 3 ∧
    ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
      bernsteinTail (m + n) v L t := by sorry

end TroppMatrixConcentration
