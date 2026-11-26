-- Prove2me | Theorems.Thm_QuarterSumLadder_sq_mod_sixteen
-- name    : QuarterSumLadder.sq_mod_sixteen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:15.649127+00:00
-- url     : https://prove2.me/theorems/00b8a76f-f297-5913-83a6-2612b004080d
-- title:
--   Quarter Sum Ladder: sq mod sixteen
-- statement:
--   Squares modulo `16`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L23-L32
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L23-L32

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.sq_mod_sixteen (v : ℕ) :
    (((v : ℤ) ^ 2 : ℤ) : ZMod 16) = (if v % 2 = 1 then 1 else 0) +
      8 * (if v % 8 = 3 ∨ v % 8 = 5 then 1 else 0) + 4 * (if v % 4 = 2 then 1 else 0) := by sorry
