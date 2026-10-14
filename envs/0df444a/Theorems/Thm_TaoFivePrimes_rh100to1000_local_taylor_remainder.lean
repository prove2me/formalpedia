-- Prove2me | Theorems.Thm_TaoFivePrimes_rh100to1000_local_taylor_remainder
-- name    : TaoFivePrimes.rh100to1000_local_taylor_remainder
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T02:47:59.92175+00:00
-- url     : https://prove2.me/theorems/00571e86-ecab-4e18-95a1-e0305ea4b845
-- title:
--   RH height 100–1000 — local Taylor remainder bound
-- statement:
--   For every real center T with |T| at most 1000, the entire Riemann xi function is approximated by its first 272 local Taylor terms about 1/2+iT, with absolute remainder at most 10^(-365) throughout the closed unit disk. This is an analytic error bound for the existing height-100–1000 RH certificate stage. It provides no numerical coefficient enclosure and proves no critical-line placement by itself.
--
--   This follows from the uniform completed-zeta bound in the vertical strip and Cauchy estimates on radius-24 circles. The estimate is an analytic input; the finite coefficient enclosures and positivity certificates remain to be supplied.
-- source:
--   Consequence of the generic Cauchy remainder bound and the vertical-strip bound in sometik179's original proof c9908072-d99a-4431-aad8-a72c6352619a, now ordinary-syntax ACCEPTED as 30db8e24-e604-49d7-ab5c-f7b6f516651a; source modules ComplexTaylorRemainder and SharpStripBounds/LocalXiBounds. The bound |T|<=1000 and order272 are derived using the same formulas; all new numeric inequalities are proved in Lean. Theta/Mellin foundations attributed to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RH100To1000LocalAnalyticModel

theorem TaoFivePrimes.rh100to1000_local_taylor_remainder (T : ℝ) (hT : |T| ≤ 1000) (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖RH1000Analytic.CertifiedComplexTaylor.remainder
      RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center T) 272 z‖ ≤ 1/10^365 := by sorry
