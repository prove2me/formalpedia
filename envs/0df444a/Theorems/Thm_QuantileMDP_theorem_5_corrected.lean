-- Prove2me | Theorems.Thm_QuantileMDP_theorem_5_corrected
-- name    : QuantileMDP.theorem_5_corrected
-- status  : Proved
-- author  : @shuffle
-- created : 2026-11-14T01:56:23.763952+00:00
-- url     : https://prove2.me/theorems/bc49f195-b91f-4f2d-be43-2c4885a7142e
-- title:
--   Quantile MDP Theorem 5 (corrected hypothesis) — conditional quantile order passes to the common mixture
-- statement:
--   Let $\mu_i$ and $\nu_i$ be probability laws of total rewards conditional on starting state $i$, with a common starting-state distribution $p$. If
--   $$
--   Q_u(\nu_i)\le Q_u(\mu_i)\qquad\text{for every }i\text{ and }0<u<1,
--   $$
--   then the unconditional reward laws satisfy
--   $$
--   Q_\tau\left(\sum_i p_i\nu_i\right)
--   \le Q_\tau\left(\sum_i p_i\mu_i\right)
--   \qquad (0<\tau<1).
--   $$
--   The Lean statement allows arbitrary nonnegative mixture weights. For probability weights the two mixtures are the unconditional laws.
--
--   This is the mixture argument used in Appendix B.2.5 of Li, Zhong and Brandeau. The original theorem is valid for T ≥ 2 under its stated filtration: it includes times 0 through k for both chains. Applying (12) at k = T − 1 for T ≥ 2 makes both total rewards measurable with respect to the conditioning information, so their conditional quantiles are the totals themselves. The example with (B,B) and (1−B,B) only concerns the weaker hypothesis that compares future rewards after time 0. It does not satisfy (12).
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.2, Theorem 5, p. 22, and Appendix B.2.5 of arXiv v4. https://arxiv.org/abs/1711.05788v5

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Definitions.Def_QuantileMDP_quantile

open MeasureTheory Set QuantileMDP
open scoped ENNReal

theorem QuantileMDP.theorem_5_corrected {S : Type*} [Fintype S] (p : S → ℝ≥0∞)
    (μ ν : S → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hν : ∀ i, IsProbabilityMeasure (ν i))
    (h : ∀ i τ, τ ∈ Ioo (0 : ℝ) 1 → quantile (ν i) τ ≤ quantile (μ i) τ)
    (τ : ℝ) (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    quantile (∑ i, p i • ν i) τ ≤ quantile (∑ i, p i • μ i) τ := by sorry
