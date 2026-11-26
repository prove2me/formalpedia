-- Prove2me | Theorems.Thm_QuarterSumLadder_val_pos_of_ne_zero
-- name    : QuarterSumLadder.val_pos_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:57.057632+00:00
-- url     : https://prove2.me/theorems/1307171d-fa4d-46f9-b44b-c31c48bd3669
-- title:
--   Quarter Sum Ladder: val pos of ne zero
-- statement:
--   The Quarter Sum Ladder construction uses the val pos of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L27-L28
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L27-L28

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.val_pos_of_ne_zero {x : ZMod p} (hx : x ≠ 0) : 0 < x.val := by sorry
