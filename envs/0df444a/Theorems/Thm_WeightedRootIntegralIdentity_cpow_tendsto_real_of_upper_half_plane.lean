-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_cpow_tendsto_real_of_upper_half_plane
-- name    : WeightedRootIntegralIdentity.cpow_tendsto_real_of_upper_half_plane
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T20:49:11.904813+00:00
-- url     : https://prove2.me/theorems/7865a285-30f0-4edd-8214-bc3d2c811de7
-- title:
--   Upper-half-plane convergence of a principal complex power
-- statement:
--   Let $b\ne0$ and $w$ be real. For the principal complex power, approaching the nonzero real base $b$ from the upper half-plane gives
--   $$\lim_{\varepsilon\to0^+}(b+i\varepsilon)^w=b^w.$$
--
--   When $b<0$, the value on the right is the principal boundary value with argument $\pi$. This supplies the individual-factor convergence required for the weighted-root boundary integral.
-- source:
--   Principal-logarithm upper boundary convention used in the keyhole argument of K B Dave, Mathematics Stack Exchange, https://math.stackexchange.com/a/4245016.

import Mathlib

namespace WeightedRootIntegralIdentity

theorem cpow_tendsto_real_of_upper_half_plane
    (b w : ℝ) (hb : b ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => ((b : ℂ) + ε * Complex.I) ^ (w : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((b : ℂ) ^ (w : ℂ))) := by sorry

end WeightedRootIntegralIdentity
