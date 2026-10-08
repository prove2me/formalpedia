-- Prove2me | Theorems.Thm_WardropTraffic_Signal_corner_min_of_neg_partials
-- name    : WardropTraffic.Signal.corner_min_of_neg_partials
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:34.825269+00:00
-- url     : https://prove2.me/theorems/a290728a-1f75-4875-abb7-2a4469bc262a
-- title:
--   Appendix IV, p. 358 — if ∂T/∂x < 0 and ∂T/∂y < 0 at (ξ, η), the minimum cycle minimizes T
-- statement:
--   Let $\lambda > 0$, $\mu > 0$ and $\xi + \eta > 1$, let $T(x,y) = (\lambda x^2 + \mu y^2)/(x+y-1)$, and let the feasible region be $F = \{(x,y) : x \le \xi,\ y \le \eta,\ x + y > 1\}$. Suppose that both partial derivatives of $T$ at $(\xi,\eta)$ are negative, that is,
--   $$\lambda\xi^2 - \mu\eta^2 - 2\lambda\xi(1-\eta) < 0 \quad\text{and}\quad \mu\eta^2 - \lambda\xi^2 - 2\mu\eta(1-\xi) < 0.$$
--   Then $(\xi, \eta)$ minimizes $T$ over $F$:
--   $$T(\xi,\eta) \le T(x,y) \qquad \text{for all } (x,y) \in F.$$
--
--   From $(\xi,\eta)$ the only admissible changes of $x$ and $y$ are reductions; this result says that when both reductions increase the delay, the minimum cycle is the optimum cycle.
--
--   **Formalization Note** The two derivatives are written through their numerators, which carry their sign since the denominator $(\xi+\eta-1)^2$ is positive. The conclusion is global minimality over the whole feasible region, which is what the page asserts ("$T$ is minimum when $x = \xi$, $y = \eta$").
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 358, Appendix IV, last paragraph

import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem corner_min_of_neg_partials (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hsum : 1 < xi + eta)
    (hx : lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta) < 0)
    (hy : mu * eta ^ 2 - lam * xi ^ 2 - 2 * mu * eta * (1 - xi) < 0) :
    ∀ z ∈ feasibleXY xi eta, delayT lam mu xi eta ≤ delayT lam mu z.1 z.2 := by sorry

end WardropTraffic.Signal
