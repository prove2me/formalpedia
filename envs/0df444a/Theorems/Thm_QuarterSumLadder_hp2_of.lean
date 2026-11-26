-- Prove2me | Theorems.Thm_QuarterSumLadder_hp2_of
-- name    : QuarterSumLadder.hp2_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:59:34.014311+00:00
-- url     : https://prove2.me/theorems/c0488b3e-3952-576d-87ea-54ec44ecee2b
-- title:
--   Quarter Sum Ladder: hp2 of
-- statement:
--   The Quarter Sum Ladder construction uses the hp2 of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L31-L31
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L31-L31

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

theorem QuarterSumLadder.hp2_of (hp8 : p % 8 = 1) : p ≠ 2 := by sorry
