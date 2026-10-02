-- Prove2me | Theorems.Thm_SennottDP_AvgFinite_prop_6_2_3_blackwell_optimal
-- name    : SennottDP.AvgFinite.prop_6_2_3_blackwell_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T08:47:17.918354+00:00
-- url     : https://prove2.me/theorems/aa960856-403d-4aa2-b17c-71c35096baaf
-- title:
--   Proposition 6.2.3 — for finite S a stationary policy is discount optimal near α = 1 and average cost optimal
-- statement:
--   Let $\Delta$ be an MDC with a finite state space $S$ (finite action sets, nonnegative costs). Then:
--
--   1. there exist $\alpha_0 \in (0,1)$ and a stationary policy $f$ such that $f$ is $\alpha$ discount optimal for every $\alpha \in (\alpha_0, 1)$;
--   2. the policy $f$ is average cost optimal, i.e. $J_f(i) = J(i)$ for all $i$, where $J$ is the infimum of $J_\theta$ over all (history dependent, randomized) policies;
--   3. for all $i \in S$,
--   $$J(i) = \lim_{\alpha \to 1^-} (1-\alpha) V_\alpha(i) = \lim_{n \to \infty} \frac{v_{f,n}(i)}{n}. \tag{6.3}$$
--
--   A stationary policy that is discount optimal on an interval $(\alpha_0,1)$ is called Blackwell optimal. The proposition shows that for finite state spaces such a policy exists and is optimal for the average cost criterion, so the search for average cost optimal policies can be restricted to stationary policies.
--
--   **Formalization Note** One fixed pair $(\alpha_0, f)$ serves all three parts (the existential quantifiers come first). Optimality compares against the infimum over all general policies. All values are in `ℝ≥0∞`; $\alpha \to 1^-$ is the filter `𝓝[<] 1`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 99–100, Proposition 6.2.3, Eq. (6.3)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal Topology
open Filter

/-- Proposition 6.2.3 (Sennott, pp. 99–100). Let `Δ` be an MDC with a finite state space. Then
(i) there exist `α₀ ∈ (0,1)` and a stationary policy `f` such that `f` is `α` discount optimal for
every `α ∈ (α₀,1)`; (ii) `f` is average cost optimal; (iii)
`J(i) = lim_{α→1⁻} (1−α)V_α(i) = lim_{n→∞} v_{f,n}(i)/n` for all `i` (6.3). -/
theorem prop_6_2_3_blackwell_optimal {S : Type*} {Act : Type*} [Fintype S] (M : MDC S Act) :
    ∃ α₀ ∈ Set.Ioo (0 : ℝ) 1, ∃ f : StationaryPolicy M,
      (∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α) ∧
      IsAverageOptimal f.toPolicy ∧
      ∀ i : S,
        Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α i) (𝓝[<] 1)
            (𝓝 (avgValue M i)) ∧
        Tendsto (fun n : ℕ => horizonCost f.toPolicy n i / (n : ℝ≥0∞)) atTop
            (𝓝 (avgValue M i)) := by sorry

end SennottDP.AvgFinite
