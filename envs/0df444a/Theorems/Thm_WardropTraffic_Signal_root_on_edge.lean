-- Prove2me | Theorems.Thm_WardropTraffic_Signal_root_on_edge
-- name    : WardropTraffic.Signal.root_on_edge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:40.341751+00:00
-- url     : https://prove2.me/theorems/4f37f376-f58a-4a51-aebd-a3bf2a30f1c1
-- title:
--   Appendix IV, p. 359 — if D < 0, x₀ = 1 − η + √{(1 − η)² + (μ/λ)η²} is the unique root of λx² − μη² − 2λx(1 − η) = 0 in (0, ξ)
-- statement:
--   Let $\lambda > 0$, $\mu > 0$, $\xi > 0$, $\eta > 0$, and suppose that
--   $$D = \frac{\mu}{\lambda}\eta^2 + 2\xi(1-\eta) - \xi^2 < 0.$$
--   Put $x_0 = 1 - \eta + \sqrt{(1-\eta)^2 + (\mu/\lambda)\eta^2}$. Then
--   1. $x_0$ solves $\lambda x^2 - \mu\eta^2 - 2\lambda x(1-\eta) = 0$, the equation $\partial T/\partial x = 0$ on the edge $y = \eta$;
--   2. $0 < x_0 < \xi$;
--   3. $x_0$ is the only solution of that equation in the interval $0 < x < \xi$.
--
--   When the minimum-cycle criterion fails, $x_0$ is the effective-red fraction of phase 1 at the optimum, while phase 2 stays saturated ($y = \eta$).
--
--   **Formalization Note** The page writes the range as "$0 < x < \eta$"; since $x$ is bounded by $\xi$ (the constraint $x \le \xi$), this is a slip for $0 < x < \xi$, which is what is stated. $x_0$ is the definition `edgeRoot lam mu eta`.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 359, Appendix IV, "The root of this equation, in the range 0 < x < η, is"

import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem root_on_edge (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hxi0 : 0 < xi) (heta0 : 0 < eta) (hD : cornerD lam mu xi eta < 0) :
    lam * edgeRoot lam mu eta ^ 2 - mu * eta ^ 2 - 2 * lam * edgeRoot lam mu eta * (1 - eta) = 0 ∧
      0 < edgeRoot lam mu eta ∧ edgeRoot lam mu eta < xi ∧
      ∀ x : ℝ, 0 < x → x < xi → lam * x ^ 2 - mu * eta ^ 2 - 2 * lam * x * (1 - eta) = 0 →
        x = edgeRoot lam mu eta := by sorry

end WardropTraffic.Signal
