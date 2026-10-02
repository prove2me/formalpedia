-- Prove2me | Theorems.Thm_SennottDP_AvgFinite_prop_6_2_2_stationary_limits
-- name    : SennottDP.AvgFinite.prop_6_2_2_stationary_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T08:44:01.512723+00:00
-- url     : https://prove2.me/theorems/2429c728-8c19-4abd-9b9a-51deed19b982
-- title:
--   Proposition 6.2.2 — for finite S and stationary e, J_e(i) = lim (1−α)V_{e,α}(i) = lim v_{e,n}(i)/n
-- statement:
--   Let $e$ be a stationary policy in an MDC with a finite state space $S$. Then
--   $$J_e(i) = \lim_{\alpha \to 1^-} (1-\alpha) V_{e,\alpha}(i) = \lim_{n \to \infty} \frac{v_{e,n}(i)}{n}, \qquad i \in S. \tag{6.2}$$
--
--   In particular, for stationary policies on finite state spaces the $\limsup$ in the definition of the average cost is a genuine limit and coincides with the vanishing-discount limit; Example 6.2.1 shows that this fails for general policies.
--
--   **Formalization Note** Both limits are stated in `ℝ≥0∞` (`Tendsto` along `𝓝[<] 1` and `atTop`) with limit $J_e(i)$; finiteness of $J_e(i)$ is not part of the statement.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 99, Proposition 6.2.2, Eq. (6.2)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal Topology
open Filter

/-- Proposition 6.2.2 (Sennott, p. 99). Let `e` be a stationary policy in an MDC with a finite state
space. Then for every `i`,
`J_e(i) = lim_{α→1⁻} (1−α)V_{e,α}(i) = lim_{n→∞} v_{e,n}(i)/n` (6.2). -/
theorem prop_6_2_2_stationary_limits {S : Type*} {Act : Type*} [Fintype S] (M : MDC S Act)
    (e : StationaryPolicy M) (i : S) :
    Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discCost e.toPolicy α i) (𝓝[<] 1)
        (𝓝 (avgCost e.toPolicy i)) ∧
    Tendsto (fun n : ℕ => horizonCost e.toPolicy n i / (n : ℝ≥0∞)) atTop
        (𝓝 (avgCost e.toPolicy i)) := by sorry

end SennottDP.AvgFinite
