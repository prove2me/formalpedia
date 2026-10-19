-- Prove2me | Theorems.Thm_StochKnapSL_CapacityGap_fill_ratio_le_prob
-- name    : StochKnapSL.CapacityGap.fill_ratio_le_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:26.202973+00:00
-- url     : https://prove2.me/theorems/50b3b3d4-267e-4586-a8c3-481578a3539b
-- title:
--   Proof of Theorem 3, p. 17 — E[x*_i] / E[d̃_i] ≤ P(x*_i > 0)
-- statement:
--   Assume the standing assumptions of §3.3: the demands $\tilde d_1, \dots, \tilde d_N$ are measurable, independent, positive and almost surely at most $\Delta > 0$, and the targets satisfy $0 \le \alpha_i \le 1$. Let $\sigma$ be a priority order, $Q \ge 0$, and $x^*_i(\sigma, \tilde d, Q)$ the greedy fractional fill of customer $i$. Then
--   $$ \frac{\mathbf E\big[x^*_i(\sigma, \tilde d, Q)\big]}{\mathbf E[\tilde d_i]} \le \mathbf P\big(x^*_i(\sigma, \tilde d, Q) > 0\big). $$
--
--   The proof of Theorem 3 rounds every positive greedy fill up to full service. This inequality shows that the resulting Type-I service probability is at least the Type-II fill rate.
--
--   **Formalization Note.** The paper writes the left side as $\mathbf E[x^*_i]/\mathbf E[x^*_i \mid x^*_i > 0]$ and bounds the conditional expectation by $\mathbf E[\tilde d_i]$. Only the resulting inequality is stated here. Positivity of the demands makes $\mathbf E[\tilde d_i] > 0$, so the division is genuine.
-- source:
--   Lyu, Chou, Teo, Zheng & Zhong, Stochastic Knapsack Revisited: The Service Level Perspective, SSRN working paper 3674463 (version of 2021-05-29), p. 17, proof of Theorem 3 (display after 'Furthermore, since we assume …')

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory

namespace StochKnapSL.CapacityGap

/-- Proof of Theorem 3, p. 17: `E[x*_i] / E[d_i] ≤ P(x*_i > 0)` for the greedy fill of any
priority order and any capacity. -/
theorem fill_ratio_le_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ)
    (hS : Standing μ d Δ α) (σ : Equiv.Perm (Fin N)) (Q : ℝ) (hQ : 0 ≤ Q) (i : Fin N) :
    (∫ ω, fill σ Q (fun j => d j ω) i ∂μ) / (∫ ω, d i ω ∂μ) ≤
      μ.real {ω | 0 < fill σ Q (fun j => d j ω) i} := by sorry

end StochKnapSL.CapacityGap
