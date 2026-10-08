-- Prove2me | Theorems.Thm_WardropTraffic_Signal_corner_condition_iff
-- name    : WardropTraffic.Signal.corner_condition_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:41.359523+00:00
-- url     : https://prove2.me/theorems/3e7bc004-1274-4520-9567-2e4ffd6175fb
-- title:
--   Appendix IV, p. 359 — λξ² − μη² − 2λξ(1 − η) < 0 iff (μ/λ)η² + 2ξ(1 − η) − ξ² > 0
-- statement:
--   Let $\lambda > 0$ and let $\mu, \xi, \eta$ be real numbers. Then
--   $$\lambda\xi^2 - \mu\eta^2 - 2\lambda\xi(1-\eta) < 0 \iff \frac{\mu}{\lambda}\eta^2 + 2\xi(1-\eta) - \xi^2 > 0.$$
--
--   The left side is the condition $[\partial T/\partial x]_{\xi,\eta} < 0$; the right side, $D > 0$, is the form in which Wardrop states the criterion for the minimum cycle to be optimal.
--
--   **Formalization Note** $D$ is the definition `cornerD lam mu xi eta`.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 359, Appendix IV, "that is to say … or …"

import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

namespace WardropTraffic.Signal

theorem corner_condition_iff (lam mu xi eta : ℝ) (hlam : 0 < lam) :
    lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta) < 0 ↔ 0 < cornerD lam mu xi eta := by sorry

end WardropTraffic.Signal
