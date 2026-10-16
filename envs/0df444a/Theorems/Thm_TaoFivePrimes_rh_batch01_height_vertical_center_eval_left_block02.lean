-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_left_block02
-- name    : TaoFivePrimes.rh_batch01_height_vertical_center_eval_left_block02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T23:03:00.262703+00:00
-- url     : https://prove2.me/theorems/51e5ff2e-588e-4838-bfc4-bea80398ad8f
-- title:
--   TaoFivePrimes.rh_batch01_height_vertical_center_eval_left_block02
-- statement:
--   Exact stable48-term integer Horner evaluation of8 vertical jet orders at theleft points32..47, after80-bit rounding. Uses proposed combined center values; mathematical interpretation requires separate center packet and analytic error proofs. No sign, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsLeft

theorem TaoFivePrimes.rh_batch01_height_vertical_center_eval_left_block02 :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesLeft.values (32+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHBatch01ContourCoefficientData.decode (((((RHBatch01VerticalJetsLeft.rows)[(8*(32+i)+k)/512]?).getD [])[((8*(32+i)+k)%512)]?).getD 0)))) := by sorry
