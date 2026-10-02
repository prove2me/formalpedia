-- Prove2me | Theorems.Thm_SennottDP_AvgFinite_prop_4_5_4_monotone_left_continuous
-- name    : SennottDP.AvgFinite.prop_4_5_4_monotone_left_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T08:29:15.682201+00:00
-- url     : https://prove2.me/theorems/a7f0f167-ae97-4504-8bda-8557045b61b3
-- title:
--   Proposition 4.5.4 — V_α is increasing and left continuous in α ∈ (0,1)
-- statement:
--   Let $\Delta$ be an MDC with countable state space. For every state $i$, the discounted value function $\alpha \mapsto V_\alpha(i) \in [0,\infty]$ is increasing (nondecreasing) on $(0,1)$ and left continuous at every $\beta \in (0,1)$:
--   $$V_\alpha(i) \le V_\beta(i) \ \ (0 < \alpha \le \beta < 1), \qquad \lim_{\alpha \to \beta^-} V_\alpha(i) = V_\beta(i).$$
--
--   Monotonicity and left continuity are the basic regularity of the optimal discounted cost in the discount factor for countable state spaces, where $V_\alpha$ may be infinite.
--
--   **Formalization Note** Values are in `ℝ≥0∞` with its order topology; left continuity is `ContinuousWithinAt … (Set.Iio β) β`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 72, Proposition 4.5.4

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal

/-- Proposition 4.5.4 (Sennott, p. 72). For an MDC with countable state space, the discounted value
function `V_α(i)` (valued in `[0,∞]`) is increasing (nondecreasing) and left continuous in
`α ∈ (0,1)`, for every state `i`. -/
theorem prop_4_5_4_monotone_left_continuous {S : Type*} {Act : Type*} [Countable S]
    (M : MDC S Act) (i : S) :
    MonotoneOn (fun α : ℝ => discValue M α i) (Set.Ioo 0 1) ∧
    ∀ β ∈ Set.Ioo (0 : ℝ) 1,
      ContinuousWithinAt (fun α : ℝ => discValue M α i) (Set.Iio β) β := by sorry

end SennottDP.AvgFinite
