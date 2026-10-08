-- Prove2me | Theorems.Thm_WardropTraffic_Signal_partials_at_corner
-- name    : WardropTraffic.Signal.partials_at_corner
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:32.904396+00:00
-- url     : https://prove2.me/theorems/34baee9c-035d-4ee4-8cdc-08999fc21fac
-- title:
--   Appendix IV, p. 358 — ∂T/∂x and ∂T/∂y at the minimum-cycle corner (ξ, η)
-- statement:
--   Let $\lambda, \mu, \xi, \eta$ be real numbers with $\xi + \eta > 1$, and let $T(x,y) = (\lambda x^2 + \mu y^2)/(x + y - 1)$. Then the partial derivatives of $T$ at the point $(\xi, \eta)$ are
--   $$\left[\frac{\partial T}{\partial x}\right]_{\xi,\eta} = \frac{\lambda\xi^2 - \mu\eta^2 - 2\lambda\xi(1-\eta)}{(\xi+\eta-1)^2}, \qquad \left[\frac{\partial T}{\partial y}\right]_{\xi,\eta} = \frac{\mu\eta^2 - \lambda\xi^2 - 2\mu\eta(1-\xi)}{(\xi+\eta-1)^2}.$$
--
--   The point $(\xi,\eta)$ corresponds to the shortest cycle compatible with the flows (both green periods saturated). The signs of these two derivatives decide whether lengthening the cycle can reduce the average delay.
--
--   **Formalization Note** Each partial derivative is stated as `HasDerivAt` of the one-variable section of $T$ (in $x$ with $y = \eta$ fixed, and in $y$ with $x = \xi$ fixed). The hypothesis $\xi + \eta > 1$ keeps the point off the pole $x + y = 1$.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 358, Appendix IV, [∂T/∂x]_{ξ,η} and [∂T/∂y]_{ξ,η}

import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem partials_at_corner (lam mu xi eta : ℝ) (hsum : 1 < xi + eta) :
    HasDerivAt (fun x => delayT lam mu x eta)
        ((lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta)) / (xi + eta - 1) ^ 2) xi ∧
      HasDerivAt (fun y => delayT lam mu xi y)
        ((mu * eta ^ 2 - lam * xi ^ 2 - 2 * mu * eta * (1 - xi)) / (xi + eta - 1) ^ 2) eta := by sorry

end WardropTraffic.Signal
