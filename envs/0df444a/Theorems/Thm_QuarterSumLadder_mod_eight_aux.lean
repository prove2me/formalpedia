-- Prove2me | Theorems.Thm_QuarterSumLadder_mod_eight_aux
-- name    : QuarterSumLadder.mod_eight_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:09.350931+00:00
-- url     : https://prove2.me/theorems/4ef4ea15-7c9f-51dd-adec-7dbe329471de
-- title:
--   Quarter Sum Ladder: mod eight aux
-- statement:
--   The Quarter Sum Ladder construction uses the mod eight aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L22-L22
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L22-L22

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem QuarterSumLadder.mod_eight_aux (hp8 : p % 8 = 1) : p - 1 = 4 * Q p := by sorry
