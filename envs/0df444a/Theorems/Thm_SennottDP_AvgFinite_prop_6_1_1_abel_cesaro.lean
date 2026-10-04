-- Prove2me | Theorems.Thm_SennottDP_AvgFinite_prop_6_1_1_abel_cesaro
-- name    : SennottDP.AvgFinite.prop_6_1_1_abel_cesaro
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T08:40:09.811981+00:00
-- url     : https://prove2.me/theorems/24afbe09-8b8b-41b1-add6-3e3409f7338d
-- title:
--   Proposition 6.1.1 — J*_θ ≤ liminf (1−α)V_{θ,α} ≤ limsup (1−α)V_{θ,α} ≤ J_θ, and the three equivalent limit conditions
-- statement:
--   Let $\Delta$ be an MDC with countable state space. For any policy $\theta$ and initial state $i$,
--   $$J^*_\theta(i) \le \liminf_{\alpha \to 1^-} (1-\alpha) V_{\theta,\alpha}(i) \le \limsup_{\alpha \to 1^-} (1-\alpha) V_{\theta,\alpha}(i) \le J_\theta(i). \tag{6.1}$$
--   Moreover the following are equivalent:
--
--   1. all the terms in (6.1) are equal and finite;
--   2. $J^*_\theta(i) = J_\theta(i) < \infty$, and hence the quantity in (2.15) is obtained as a limit;
--   3. $\lim_{\alpha \to 1^-} (1-\alpha) V_{\theta,\alpha}(i)$ exists and is finite.
--
--   This is the link between the discounted and the average cost criteria that Chapter 6 builds on: the average cost of a policy is controlled by the discounted cost scaled by $1-\alpha$ as $\alpha \to 1^-$.
--
--   **Formalization Note** All terms are in `ℝ≥0∞` (they may be $+\infty$). $\alpha \to 1^-$ is the filter `𝓝[<] 1` on ℝ, and $1-\alpha$ enters as `ENNReal.ofReal (1 - α)`. The equivalence is a `List.TFAE`; the clause "hence the quantity in (2.15) is obtained as a limit" is stated as a separate implication: under (ii), $v_{\theta,n}(i)/n \to J_\theta(i)$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 98, Proposition 6.1.1, Eq. (6.1)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal Topology
open Filter

/-- Proposition 6.1.1 (Sennott, p. 98). For an MDC with countable state space, any policy `θ` and
initial state `i`,
`J*_θ(i) ≤ liminf_{α→1⁻} (1−α)V_{θ,α}(i) ≤ limsup_{α→1⁻} (1−α)V_{θ,α}(i) ≤ J_θ(i)` (6.1),
and the following are equivalent: (i) all the terms in (6.1) are equal and finite;
(ii) `J*_θ(i) = J_θ(i) < ∞`; (iii) `lim_{α→1⁻} (1−α)V_{θ,α}(i)` exists and is finite. Moreover
under (ii) the quantity in (2.15) is obtained as a limit. -/
theorem prop_6_1_1_abel_cesaro {S : Type*} {Act : Type*} [Countable S] (M : MDC S Act)
    (θ : Policy M) (i : S) :
    let F : ℝ → ℝ≥0∞ := fun α => ENNReal.ofReal (1 - α) * discCost θ α i
    avgCostLiminf θ i ≤ liminf F (𝓝[<] (1 : ℝ)) ∧
    liminf F (𝓝[<] (1 : ℝ)) ≤ limsup F (𝓝[<] (1 : ℝ)) ∧
    limsup F (𝓝[<] (1 : ℝ)) ≤ avgCost θ i ∧
    List.TFAE
      [ avgCostLiminf θ i = liminf F (𝓝[<] (1 : ℝ)) ∧
          liminf F (𝓝[<] (1 : ℝ)) = limsup F (𝓝[<] (1 : ℝ)) ∧
          limsup F (𝓝[<] (1 : ℝ)) = avgCost θ i ∧ avgCost θ i < ⊤,
        avgCostLiminf θ i = avgCost θ i ∧ avgCost θ i < ⊤,
        ∃ L : ℝ≥0∞, L < ⊤ ∧ Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 L) ] ∧
    (avgCostLiminf θ i = avgCost θ i ∧ avgCost θ i < ⊤ →
      Tendsto (fun n : ℕ => horizonCost θ n i / (n : ℝ≥0∞)) atTop (𝓝 (avgCost θ i))) := by sorry

end SennottDP.AvgFinite
