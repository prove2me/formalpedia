-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch7_intrinsic_bernstein_expectation
-- name    : TroppMatrixConcentration.ch7_intrinsic_bernstein_expectation
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:53:18.356123+00:00
-- url     : https://prove2.me/theorems/24efe2e9-323a-4409-b95e-a601fe505486
-- title:
--   Corollary 7.3.2 — Intrinsic Bernstein expectation bound
-- statement:
--   There exists a universal real constant $C>0$ such that the following holds for every probability space and every finite independent family of measurable complex $m\times n$ random matrices $S_k$, $m,n\ge1$, with mean zero and $\|S_k\|\le L$ almost surely for $L\ge0$. Set $Z=\sum_kS_k$. For semidefinite upper bounds $V_1\succeq\mathbb EZZ^*$ and $V_2\succeq\mathbb EZ^*Z$, at least one nonzero, set $r=r(\operatorname{diag}(V_1,V_2))$ and $v=\max\{\|V_1\|,\|V_2\|\}$. Then
--   $$\mathbb E\|Z\|\le C\left(\sqrt{v\log(1+r)}+L\log(1+r)\right).$$
--   The constant is quantified before all probability spaces, dimensions, summands, bounds, and proxies, so it cannot depend on any of them. No explicit numerical constant is specified by the corollary.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Corollary 7.3.2, equation (7.3.3), printed p. 109; Section 7.7.4, printed pp. 117–118.

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch7_intrinsic_bernstein_expectation :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {m n N : ℕ} [NeZero m] [NeZero n]
      (S : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ) (L : ℝ), 0 ≤ L →
    ∀ (V₁ : Matrix (Fin m) (Fin m) ℂ) (V₂ : Matrix (Fin n) (Fin n) ℂ),
      (V₁ ≠ 0 ∨ V₂ ≠ 0) →
      (∀ k, Measurable (S k)) → iIndepFun S μ →
      (∀ k, (∫ ω, S k ω ∂μ) = 0) →
      (∀ k, ∀ᵐ ω ∂μ, spectralNorm (S k ω) ≤ L) →
      loewnerLE (∫ ω, (∑ k, S k ω) * (∑ k, S k ω).conjTranspose ∂μ) V₁ →
      loewnerLE (∫ ω, (∑ k, S k ω).conjTranspose * (∑ k, S k ω) ∂μ) V₂ →
      let r := intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂)
      let v := max (spectralNorm V₁) (spectralNorm V₂)
      (∫ ω, spectralNorm (∑ k, S k ω) ∂μ) ≤
        C * (Real.sqrt (v * Real.log (1 + r)) + L * Real.log (1 + r)) := by sorry

end TroppMatrixConcentration
