-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_center_point_enclosure
-- name    : TaoFivePrimes.rh_batch01_height_center_point_enclosure
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T19:03:47.227093+00:00
-- url     : https://prove2.me/theorems/2a3d08ec-3f41-415f-9ca4-24ce967faa3b
-- title:
--   TaoFivePrimes.rh_batch01_height_center_point_enclosure
-- statement:
--   A1e-12 enclosure for any of the8 actual vertical polynomial jets at any of the129 proposed edge points, from explicit55 center-coefficient enclosures and exact48-term Horner evaluation/rounding. Proves the scaled analytic Taylor tail using total Fourier coefficient mass, center-error propagation, stable Horner rounding and80-bit final rounding. The center bounds and exact evaluation equality are explicit prerequisites. No winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenter
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalAnalyticValues
import Definitions.Def_TaoFivePrimes_RHBatch01PolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighContourVector

theorem TaoFivePrimes.rh_batch01_height_center_point_enclosure (t : Fin 3) (cs : List (Int×Int)) (j k : Nat) (hj:j≤128) (hk:k<8)
 (hc:∀n:Nat,n<55 →
  let p:=(cs[n]?).getD (0,0)
  ‖((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128-RHBatch01VerticalAnalyticValues.center t n‖≤2048/10^18)
 (p : Int×Int) (hp:p=((RHBatch01VerticalCenter.evaluate cs j k).1/(2:Int)^48,(RHBatch01VerticalCenter.evaluate cs j k).2/(2:Int)^48)) :
 ‖RHBatch01PolynomialJet.jet (64*((t.val:ℂ)-1)+(-1/2+(j:ℂ)/128)*Complex.I) (Complex.I/128) k-RHHighContourVector.value p‖≤1/10^12 := by sorry
