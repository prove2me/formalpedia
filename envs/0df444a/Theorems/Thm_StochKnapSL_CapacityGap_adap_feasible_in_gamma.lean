-- Prove2me | Theorems.Thm_StochKnapSL_CapacityGap_adap_feasible_in_gamma
-- name    : StochKnapSL.CapacityGap.adap_feasible_in_gamma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:20.351619+00:00
-- url     : https://prove2.me/theorems/e6ae4853-2afc-454a-9cb7-06e9bc6a34b3
-- title:
--   Proof of Theorem 4, p. 37 — if Q is feasible for adaptive policies, then α ∈ Γ(Q + Δ)
-- statement:
--   Assume the standing assumptions of §3.3. If capacity $Q \ge 0$ lets some randomized adaptive policy fully serve every customer $i$ with probability at least $\alpha_i$, then $\alpha \in \Gamma(Q + \Delta)$:
--   $$ \sum_{k\in U} \mathbf E[\tilde d_k]\, \alpha_k \le \mathbf E\Big[\min\Big\{\sum_{k\in U}\tilde d_k,\ Q + \Delta\Big\}\Big] \qquad \text{for all } U \subseteq \{1,\dots,N\}. $$
--   So $Q + \Delta$ is feasible for the Type-II problem (CPP-B).
--
--   Taking the infimum over feasible $Q$ gives Theorem 4.
-- source:
--   Lyu, Chou, Teo, Zheng & Zhong, Stochastic Knapsack Revisited: The Service Level Perspective, SSRN working paper 3674463 (version of 2021-05-29), p. 37, proof of Theorem 4 (Appendix A.3)

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory

namespace StochKnapSL.CapacityGap

/-- Proof of Theorem 4, p. 37: if capacity `Q` is feasible for adaptive policies, then
`α ∈ Γ(Q + Δ)`. -/
theorem adap_feasible_in_gamma {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ)
    (hS : Standing μ d Δ α) (Q : ℝ) (hQ : AdapFeasible μ d α Q) :
    InGamma μ d α (Q + Δ) := by sorry

end StochKnapSL.CapacityGap
