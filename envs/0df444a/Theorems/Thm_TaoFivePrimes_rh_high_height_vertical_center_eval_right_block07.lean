-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_eval_right_block07
-- name    : TaoFivePrimes.rh_high_height_vertical_center_eval_right_block07
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T12:19:27.856077+00:00
-- url     : https://prove2.me/theorems/6085a8b4-83d5-4663-9982-8d137ad119ff
-- title:
--   TaoFivePrimes.rh_high_height_vertical_center_eval_right_block07
-- statement:
--   Exact stable48-term integer Horner evaluation of8 vertical jet orders at theright points112..127, after80-bit rounding. Uses proposed combined center values; mathematical interpretation requires separate center packet and analytic error proofs. No sign, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesRight
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsRight

theorem TaoFivePrimes.rh_high_height_vertical_center_eval_right_block07 :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesRight.values (112+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHHighContourCoefficientData.decode (((((RHHighVerticalJetsRight.rows)[(8*(112+i)+k)/512]?).getD [])[((8*(112+i)+k)%512)]?).getD 0)))) := by sorry
