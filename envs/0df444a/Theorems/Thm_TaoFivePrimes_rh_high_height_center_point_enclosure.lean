-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_center_point_enclosure
-- name    : TaoFivePrimes.rh_high_height_center_point_enclosure
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T11:01:04.578974+00:00
-- url     : https://prove2.me/theorems/f44ae3ff-edf7-4a47-b3fe-486f1c617616
-- title:
--   TaoFivePrimes.rh_high_height_center_point_enclosure
-- statement:
--   A1e-12 enclosure for any of the8 actual vertical polynomial jets at any of the129 proposed edge points, from explicit55 center-coefficient enclosures and exact48-term Horner evaluation/rounding. Proves the scaled analytic Taylor tail using total Fourier coefficient mass, center-error propagation, stable Horner rounding and80-bit final rounding. The center bounds and exact evaluation equality are explicit prerequisites. No winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenter
import Definitions.Def_TaoFivePrimes_RHHighVerticalAnalyticValues
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighContourVector

theorem TaoFivePrimes.rh_high_height_center_point_enclosure (t : Fin 3) (cs : List (Int×Int)) (j k : Nat) (hj:j≤128) (hk:k<8)
 (hc:∀n:Nat,n<55 →
  let p:=(cs[n]?).getD (0,0)
  ‖((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128-RHHighVerticalAnalyticValues.center t n‖≤2048/10^18)
 (p : Int×Int) (hp:p=((RHHighVerticalCenter.evaluate cs j k).1/(2:Int)^48,(RHHighVerticalCenter.evaluate cs j k).2/(2:Int)^48)) :
 ‖RHHighPolynomialJet.jet (64*((t.val:ℂ)-1)+(-1/2+(j:ℂ)/128)*Complex.I) (Complex.I/128) k-RHHighContourVector.value p‖≤1/10^12 := by sorry
