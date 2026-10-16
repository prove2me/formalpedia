-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_eval_right_block01
-- name    : TaoFivePrimes.rh_high_height_vertical_center_eval_right_block01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T11:03:09.400974+00:00
-- url     : https://prove2.me/theorems/b134afe1-ac82-4ffe-a265-109f340fd7b0
-- title:
--   TaoFivePrimes.rh_high_height_vertical_center_eval_right_block01
-- statement:
--   Exact stable48-term integer Horner evaluation of8 vertical jet orders at theright points16..31, after80-bit rounding. Uses proposed combined center values; mathematical interpretation requires separate center packet and analytic error proofs. No sign, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsRight

theorem TaoFivePrimes.rh_high_height_vertical_center_eval_right_block01 :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesRight.values (16+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHHighContourCoefficientData.decode (((((RHHighVerticalJetsRight.rows)[(8*(16+i)+k)/512]?).getD [])[((8*(16+i)+k)%512)]?).getD 0)))) := by sorry
