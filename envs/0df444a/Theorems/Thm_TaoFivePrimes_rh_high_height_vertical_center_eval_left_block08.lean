-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_eval_left_block08
-- name    : TaoFivePrimes.rh_high_height_vertical_center_eval_left_block08
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:36:07.970103+00:00
-- url     : https://prove2.me/theorems/9e46dd4b-fcd2-4287-a11a-3974f01a009e
-- title:
--   TaoFivePrimes.rh_high_height_vertical_center_eval_left_block08
-- statement:
--   Exact stable48-term integer Horner evaluation of8 vertical jet orders at theleft points128..128, after80-bit rounding. Uses proposed combined center values; mathematical interpretation requires separate center packet and analytic error proofs. No sign, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHHighVerticalJetsLeft

theorem TaoFivePrimes.rh_high_height_vertical_center_eval_left_block08 :
 ((List.range 1).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHHighVerticalCenter.evaluate RHHighVerticalCenterValuesLeft.values (128+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 1).map (fun i=>(List.range 8).map (fun k=>
  RHHighContourCoefficientData.decode (((((RHHighVerticalJetsLeft.rows)[(8*(128+i)+k)/512]?).getD [])[((8*(128+i)+k)%512)]?).getD 0)))) := by sorry
