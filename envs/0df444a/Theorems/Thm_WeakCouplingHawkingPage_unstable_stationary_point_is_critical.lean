-- Prove2me | Theorems.Thm_WeakCouplingHawkingPage_unstable_stationary_point_is_critical
-- name    : WeakCouplingHawkingPage.unstable_stationary_point_is_critical
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T02:29:47.556303+00:00
-- url     : https://prove2.me/theorems/274ee2ef-7894-52cc-8110-86d230424ec9
-- title:
--   The intervening stationary point is a strict local maximum
-- statement:
--   Let $\alpha$, $b$, and $u$ be real numbers with $b<0$ and $0<u<1/2$. If $\alpha=-2bu^2$, then the derivative of $V_{\alpha,b}(u)=\alpha u^2+bu^4$ vanishes at $u$, and its second derivative there is negative:
--
--   $$V'_{\alpha,b}(u)=2\alpha u+4bu^3=0,\qquad V''_{\alpha,b}(u)=2\alpha+12bu^2<0.$$
--
--   Thus any point in the ungapped interval satisfying this relation is a strict local maximum of the polynomial potential, matching the paper's unstable intermediate saddle.
-- source:
--   Claude (Anthropic), The Hawking–Page transition at weak coupling, version 1 (November 2026), https://hexagonmath.org/pdf/2611.00175v1, §3.3, eq. (22) and Table 2

import Mathlib
import Definitions.Def_WeakCouplingLandauPolynomial

namespace WeakCouplingHawkingPage

theorem unstable_stationary_point_is_critical (alpha b u : ℝ)
    (hb : b < 0) (hu : 0 < u) (hu_half : u < 1 / 2)
    (hstationary : alpha = -2 * b * u ^ 2) :
    2 * alpha * u + 4 * b * u ^ 3 = 0 ∧
      2 * alpha + 12 * b * u ^ 2 < 0 := by sorry

end WeakCouplingHawkingPage
