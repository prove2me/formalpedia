-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_right_block04
-- name    : TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block04
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T08:50:15.927225+00:00
-- url     : https://prove2.me/theorems/436273c9-33e0-4919-b033-e4c591991fb5
-- title:
--   TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block04
-- statement:
--   Exact stable48-term integer Horner evaluation of8 vertical jet orders at theright points64..79, after80-bit rounding. Uses proposed combined center values; mathematical interpretation requires separate center packet and analytic error proofs. No sign, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsRight

theorem TaoFivePrimes.rh_batch01_height_vertical_center_eval_right_block04 :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesRight.values (64+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHBatch01ContourCoefficientData.decode (((((RHBatch01VerticalJetsRight.rows)[(8*(64+i)+k)/512]?).getD [])[((8*(64+i)+k)%512)]?).getD 0)))) := by sorry
