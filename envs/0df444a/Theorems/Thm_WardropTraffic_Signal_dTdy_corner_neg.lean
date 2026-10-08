-- Prove2me | Theorems.Thm_WardropTraffic_Signal_dTdy_corner_neg
-- name    : WardropTraffic.Signal.dTdy_corner_neg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:38.819495+00:00
-- url     : https://prove2.me/theorems/17b5341f-8436-4056-a5de-d409d8257550
-- title:
--   Appendix IV, p. 359 — (ξ + η − 1)²[∂T/∂y] = −μ{2η(1 − η) + (ξ − η)²} − (λ − μ)ξ² < 0 when λ ≥ μ
-- statement:
--   Let $\mu > 0$, $\lambda \ge \mu$, $0 < \eta < 1$ and $\xi + \eta > 1$. Then the numerator of $[\partial T/\partial y]_{\xi,\eta}$ satisfies
--   $$\mu\eta^2 - \lambda\xi^2 - 2\mu\eta(1-\xi) = \mu(\eta^2 - 2\eta + 2\xi\eta) - \lambda\xi^2 = -\mu\{2\eta(1-\eta) + (\xi-\eta)^2\} - (\lambda-\mu)\xi^2,$$
--   and consequently
--   $$\left[\frac{\partial T}{\partial y}\right]_{\xi,\eta} = \frac{\mu\eta^2 - \lambda\xi^2 - 2\mu\eta(1-\xi)}{(\xi+\eta-1)^2} < 0.$$
--
--   The phases can always be labelled so that $\lambda \ge \mu$; with that labelling, shortening the phase-2 effective red from the minimum cycle never helps, and only the sign of $\partial T/\partial x$ remains to be examined.
--
--   **Formalization Note** The page prints $(\xi+\eta)^2$ inside the braces; expanding $\mu(\eta^2 - 2\eta + 2\xi\eta) - \mu\xi^2 = -\mu(2\eta - \eta^2 - 2\xi\eta + \xi^2)$ shows the correct term is $(\xi-\eta)^2$, which is what is stated. The strict inequality uses $\mu > 0$ and $0 < \eta < 1$ (so that $2\eta(1-\eta) > 0$) together with $\lambda \ge \mu$.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 359, Appendix IV, first display and the paragraph "Suppose that λ ≥ μ"

import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem dTdy_corner_neg (lam mu xi eta : ℝ) (hmu : 0 < mu) (hlm : mu ≤ lam)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hsum : 1 < xi + eta) :
    mu * eta ^ 2 - lam * xi ^ 2 - 2 * mu * eta * (1 - xi) =
        mu * (eta ^ 2 - 2 * eta + 2 * xi * eta) - lam * xi ^ 2 ∧
      mu * (eta ^ 2 - 2 * eta + 2 * xi * eta) - lam * xi ^ 2 =
        -mu * (2 * eta * (1 - eta) + (xi - eta) ^ 2) - (lam - mu) * xi ^ 2 ∧
      (mu * eta ^ 2 - lam * xi ^ 2 - 2 * mu * eta * (1 - xi)) / (xi + eta - 1) ^ 2 < 0 := by sorry

end WardropTraffic.Signal
