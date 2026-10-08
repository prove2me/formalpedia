-- Prove2me | Theorems.Thm_WardropTraffic_Signal_optimum_phase_times
-- name    : WardropTraffic.Signal.optimum_phase_times
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:53.401588+00:00
-- url     : https://prove2.me/theorems/87f47d60-2658-480a-ad55-dec989f7c7c4
-- title:
--   Appendix IV, pp. 358–359 — optimum phase times of a two-phase fixed-time signal: minimum cycle if D > 0, (x₀, η) if D ≤ 0
-- statement:
--   Let $\lambda \ge \mu > 0$, $0 < \xi < 1$, $0 < \eta < 1$ and $\xi + \eta > 1$. Let
--   $$T(x,y) = \frac{\lambda x^2 + \mu y^2}{x + y - 1}$$
--   on the feasible region $F = \{(x,y) : x \le \xi,\ y \le \eta,\ x + y > 1\}$, and put
--   $$D = \frac{\mu}{\lambda}\eta^2 + 2\xi(1-\eta) - \xi^2, \qquad x_0 = 1 - \eta + \sqrt{(1-\eta)^2 + \frac{\mu}{\lambda}\eta^2}.$$
--   Then:
--   1. if $D > 0$, the minimum cycle $(\xi,\eta)$ minimizes $T$ over $F$: $T(\xi,\eta) \le T(x,y)$ for all $(x,y) \in F$;
--   2. if $D \le 0$, the point $(x_0, \eta)$ lies in $F$ and minimizes $T$ over $F$: $T(x_0,\eta) \le T(x,y)$ for all $(x,y) \in F$.
--
--   Here $x$ and $y$ are the effective red times of the two phases as fractions of the cycle, $\xi$ and $\eta$ their largest values compatible with the flows, and $T$ the flow-weighted average delay (16). The theorem answers the question of Appendix IV: the shortest cycle (Adams' formula) minimizes the average delay exactly in the first case, and otherwise the optimum keeps phase 2 saturated and lengthens the cycle to $c = A/(x_0 + \eta - 1)$.
--
--   **Formalization Note** The theorem is stated in the reduced parameters $\lambda, \mu, \xi, \eta$ alone, which are all the argument uses; their expression through the flows is the separate theorem `original_quantities`. The hypothesis $\lambda \ge \mu$ is the page's labelling of the phases. $0 < \xi, \eta$ means $q_k < p_k$; $\xi, \eta < 1$ is printed; $\xi + \eta > 1$ means $q_1/p_1 + q_2/p_2 < 1$, without which the feasible region is empty. The final "if this condition is not satisfied" includes $D = 0$; then $x_0 = \xi$, so the formula gives the minimum cycle.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), pp. 358–359, Appendix IV

import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem optimum_phase_times (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hlm : mu ≤ lam) (hxi0 : 0 < xi) (hxi1 : xi < 1) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsum : 1 < xi + eta) :
    (0 < cornerD lam mu xi eta →
        ∀ z ∈ feasibleXY xi eta, delayT lam mu xi eta ≤ delayT lam mu z.1 z.2) ∧
      (cornerD lam mu xi eta ≤ 0 →
        (edgeRoot lam mu eta, eta) ∈ feasibleXY xi eta ∧
          ∀ z ∈ feasibleXY xi eta,
            delayT lam mu (edgeRoot lam mu eta) eta ≤ delayT lam mu z.1 z.2) := by sorry

end WardropTraffic.Signal
