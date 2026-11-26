-- Prove2me | Theorems.Thm_Sendov_B28_29_P_pos
-- name    : Sendov.B28_29.P_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:01.912024+00:00
-- url     : https://prove2.me/theorems/45da07b7-b1aa-4c96-bc6e-cc99178b98e3
-- title:
--   B28 29: P pos
-- statement:
--   The certificate: `17 ^ 26 * P α` is a positive combination of `αʲ (17-α)^(26-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L88-L153
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L88-L153

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29
set_option maxHeartbeats 2000000

theorem Sendov.B28_29.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 14) :
    0 < 426450318135882438427115499581616 + 1858834576882378710373815569972592 * α + 3736799374885893548337894566091516 * α ^ 2 + 4586209917810757974592827719731488 * α ^ 3 + 3832530771213891318426391118558376 * α ^ 4 + 2301315780911216714788724083158840 * α ^ 5 + 1020320104787175718704940125987654 * α ^ 6 + 337351267574328588560584527446352 * α ^ 7 + 82684042360278469454015755593696 * α ^ 8 + 14571761439373687941870063150072 * α ^ 9 + 1651893249078514632421437650658 * α ^ 10 + 16915365961758038105007429024 * α ^ 11 - 175858786927760049854457800868 * α ^ 12 + 13481653528168191298544554836 * α ^ 13 + 281552860237833486968732937 * α ^ 14 + 14047072236623243173813992 * α ^ 15 - 9139934377157415820848 * α ^ 16 - 45943869853012600689984 * α ^ 17 - 3291728447735177292432 * α ^ 18 - 135117714229500881664 * α ^ 19 - 3776901841060823808 * α ^ 20 - 75424649382531072 * α ^ 21 - 1084454315870976 * α ^ 22 - 11022972807168 * α ^ 23 - 75437817856 * α ^ 24 - 312639488 * α ^ 25 - 593920 * α ^ 26 := by sorry
