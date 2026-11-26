-- Prove2me | Theorems.Thm_QuarterSumLadder_odd_p
-- name    : QuarterSumLadder.odd_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:42.506018+00:00
-- url     : https://prove2.me/theorems/b4c53903-7669-593a-a545-90b712214845
-- title:
--   Quarter Sum Ladder: odd p
-- statement:
--   The Quarter Sum Ladder construction uses the odd p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L22-L22
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L22-L22

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.odd_p (hp2 : p ≠ 2) : Odd p := by sorry
