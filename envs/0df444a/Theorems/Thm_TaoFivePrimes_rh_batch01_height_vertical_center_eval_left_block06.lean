-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_center_eval_left_block06
-- name    : TaoFivePrimes.rh_batch01_height_vertical_center_eval_left_block06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:24:15.836807+00:00
-- url     : https://prove2.me/theorems/efeef8ce-164c-48b2-aad3-294492efc579
-- title:
--   TaoFivePrimes.rh_batch01_height_vertical_center_eval_left_block06
-- statement:
--   Exact stable48-term integer Horner evaluation of8 vertical jet orders at theleft points96..111, after80-bit rounding. Uses proposed combined center values; mathematical interpretation requires separate center packet and analytic error proofs. No sign, winding, count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesLeft
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalJetsLeft

theorem TaoFivePrimes.rh_batch01_height_vertical_center_eval_left_block06 :
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  let p:=RHBatch01VerticalCenter.evaluate RHBatch01VerticalCenterValuesLeft.values (96+i) k
  (p.1/(2:Int)^48,p.2/(2:Int)^48))))=
 ((List.range 16).map (fun i=>(List.range 8).map (fun k=>
  RHBatch01ContourCoefficientData.decode (((((RHBatch01VerticalJetsLeft.rows)[(8*(96+i)+k)/512]?).getD [])[((8*(96+i)+k)%512)]?).getD 0)))) := by sorry
