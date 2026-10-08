-- Prove2me | Theorems.Thm_WardropTraffic_MinTime_hasDerivAt_flow_mul_routeTime
-- name    : WardropTraffic.MinTime.hasDerivAt_flow_mul_routeTime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:59.825395+00:00
-- url     : https://prove2.me/theorems/a5d8859c-77ee-4ad1-aac6-503ed992c555
-- title:
--   (29)–(30), p. 346 — the marginal time d(qᵢtᵢ)/dqᵢ = bᵢ/(1 − qᵢ/pᵢ)², equal to bᵢ at qᵢ = 0
-- statement:
--   Let route $i$ have positive capacity constant $p_i$ and journey time $t_i(x) = b_i/(1 - x/p_i)$ (equation (22)). The contribution $x\, t_i(x)$ of the route to the number of additional vehicles en route is differentiable at every flow $x < p_i$, with
--   $$
--   \frac{d\,(x\, t_i(x))}{dx} = \frac{b_i}{(1 - x/p_i)^2}, \qquad\text{and in particular}\qquad \left[\frac{d\,(x\, t_i(x))}{dx}\right]_{x=0} = b_i .
--   $$
--   This is the **marginal journey time** of route $i$: the rate at which the total $Z$ grows when flow is added to the route. Equations (29)–(30) identify it in closed form, which the other results of this mission use in place of the derivative.
--
--   **Formalization Note** The derivative is stated with `HasDerivAt` for the one-variable function $y \mapsto y\, t_i(y)$, so no value of an undefined derivative is used. The second conjunct is (30), the case $x = 0$, stated separately as on the page.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 346, (29)–(30)

import Mathlib
import Definitions.Def_WardropTraffic_MinTime_Setting

namespace WardropTraffic.MinTime

/-- (29)–(30): the marginal journey time `d(q_i t_i)/dq_i = b_i / (1 - q_i/p_i)^2`,
equal to `b_i` at zero flow. -/
theorem hasDerivAt_flow_mul_routeTime {D : ℕ} (b p : Fin D → ℝ) (hp : ∀ i, 0 < p i)
    (i : Fin D) :
    (∀ x : ℝ, x < p i →
      HasDerivAt (fun y => y * WardropTraffic.EqualTimes.routeTime b p i y) (b i / (1 - x / p i) ^ 2) x) ∧
    HasDerivAt (fun y => y * WardropTraffic.EqualTimes.routeTime b p i y) (b i) 0 := by sorry

end WardropTraffic.MinTime
