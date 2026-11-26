-- Prove2me | Theorems.Thm_QuarterSumLadder_seventeen_le
-- name    : QuarterSumLadder.seventeen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:59.995643+00:00
-- url     : https://prove2.me/theorems/f62b752f-02c7-55d3-95a7-8e1c50390e5d
-- title:
--   Quarter Sum Ladder: seventeen le
-- statement:
--   The Quarter Sum Ladder construction uses the seventeen le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L24-L28
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L24-L28

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.seventeen_le (hp8 : p % 8 = 1) : 17 ≤ p := by sorry
