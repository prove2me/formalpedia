-- Prove2me | Theorems.Thm_QuarterSumLadder_neg_half_iff
-- name    : QuarterSumLadder.neg_half_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:56:33.989801+00:00
-- url     : https://prove2.me/theorems/0db3adf2-9027-4139-a10a-b69f67a3c3d4
-- title:
--   Quarter Sum Ladder: neg half iff
-- statement:
--   The Quarter Sum Ladder construction uses the neg half iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L41-L47
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L41-L47

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.neg_half_iff (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) :
    2 * (-x).val < p ↔ ¬ 2 * x.val < p := by sorry
