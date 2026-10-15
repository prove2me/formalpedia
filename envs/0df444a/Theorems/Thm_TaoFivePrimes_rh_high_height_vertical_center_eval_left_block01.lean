-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_eval_left_block01
-- name    : TaoFivePrimes.rh_high_height_vertical_center_eval_left_block01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:56:21.69346+00:00
-- url     : https://prove2.me/theorems/4ccff484-ccda-46cf-bbd1-4e5ccb82fffb
-- title:
--   TaoFivePrimes.rh_high_height_vertical_center_eval_left_block01
-- statement:
--   Exact stable48-term integer Horner evaluation of8 vertical jet orders at theleft points16..31, after80-bit rounding. Uses proposed combined center values; mathematical interpretation requires separate center packet and analytic error proofs. No sign, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsLeft

theorem TaoFivePrimes.rh_high_height_vertical_center_eval_left_block01 :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesLeft.values (16+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHHighContourCoefficientData.decode (((((RHHighVerticalJetsLeft.rows)[(8*(16+i)+k)/512]?).getD [])[((8*(16+i)+k)%512)]?).getD 0)))) := by sorry
