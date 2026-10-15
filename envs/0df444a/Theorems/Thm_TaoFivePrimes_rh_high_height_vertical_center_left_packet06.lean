-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_center_left_packet06
-- name    : TaoFivePrimes.rh_high_height_vertical_center_left_packet06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:17:42.091636+00:00
-- url     : https://prove2.me/theorems/8f234c43-0108-4d3e-9f4c-944a9147f120
-- title:
--   TaoFivePrimes.rh_high_height_vertical_center_left_packet06
-- statement:
--   Exact ordinary-kernel evaluation of one32-frequency packet of55 normalized center Taylor coefficients. No approximation, sign, winding, zero count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft

theorem TaoFivePrimes.rh_high_height_vertical_center_left_packet06 :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 6=((RHHighVerticalCenterLeft.rows[6]?).getD []) := by sorry
