-- Prove2me | Theorems.Thm_WardropTraffic_EqualTimes_routeTime_ge
-- name    : WardropTraffic.EqualTimes.routeTime_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:57.988703+00:00
-- url     : https://prove2.me/theorems/8bd93ab6-4070-4b76-836e-8599b9bd485a
-- title:
--   p. 345 — the journey time (22) is at least bᵢ, with equality exactly at zero additional flow
-- statement:
--   Let route $i$ have positive constants $b_i$ and $p_i$ and journey time $t_i(x) = b_i/(1 - x/p_i)$ at additional flow $x$ (equation (22)). For every flow $x$ with $0 \le x < p_i$,
--   $$
--   t_i(x) \ge b_i, \qquad\text{and}\qquad t_i(x) = b_i \iff x = 0 .
--   $$
--   So $b_i$ is the journey time of a single vehicle on an otherwise unused route, and no flow can make the route faster than that.
--
--   This is the fact behind the paper's remark that "the journey time on any route $i$ cannot be less than $b_i$", which decides which routes can be in use under the equal-times criterion.
--
--   **Formalization Note** The positivity of $b_i$, $p_i$ and the range $0 \le x < p_i$ are the model's standing conditions (positive speed); the paper presupposes them.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 345, (1) Equal Times: "Any one of these quantities bᵢ is the journey time on route i when the additional flow qᵢ = 0" and "equation (22) shows that the journey time on any route i cannot be less than bᵢ"

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

namespace WardropTraffic.EqualTimes

theorem routeTime_ge {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i)
    (i : Fin D) (x : ℝ) (hx0 : 0 ≤ x) (hxp : x < p i) :
    b i ≤ routeTime b p i x ∧ (routeTime b p i x = b i ↔ x = 0) := by sorry

end WardropTraffic.EqualTimes
