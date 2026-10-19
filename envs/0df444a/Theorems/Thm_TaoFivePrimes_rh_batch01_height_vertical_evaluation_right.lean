-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_evaluation_right
-- name    : TaoFivePrimes.rh_batch01_height_vertical_evaluation_right
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T13:32:13.665065+00:00
-- url     : https://prove2.me/theorems/3960edf5-0d46-4e2b-8a15-989f9f9198fd
-- title:
--   TaoFivePrimes.rh_batch01_height_vertical_evaluation_right
-- statement:
--   All129-by8 vertical Horner outputs equal the existing proposed80-bit jet words under the corrected512-word chunk lookup. Reuses the9 accepted bounded evaluation blocks; pure finite arithmetic, with no analytic, winding, zero-count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsRight

theorem TaoFivePrimes.rh_batch01_height_vertical_evaluation_right (j k : Nat) (hj:j≤128) (hk:k<8) :
 let p:=RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesRight.values j k
 (p.1/(2:Int)^48,p.2/(2:Int)^48)=RHHighContourVector.decode
  (((((RHBatch01VerticalJetsRight.rows)[(8*j+k)/512]?).getD [])[((8*j+k)%512)]?).getD 0) := by sorry
