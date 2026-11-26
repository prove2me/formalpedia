-- Prove2me | Theorems.Thm_QuarterSumLadder_val_two_mul_of_lt
-- name    : QuarterSumLadder.val_two_mul_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:56:21.413377+00:00
-- url     : https://prove2.me/theorems/8e948404-5b43-4da9-ba06-d3f6309836fc
-- title:
--   Quarter Sum Ladder: val two mul of lt
-- statement:
--   The Quarter Sum Ladder construction uses the val two mul of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L36-L39
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L36-L39

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.val_two_mul_of_lt {x : ZMod p} (hx : 2 * x.val < p) : (2 * x).val = 2 * x.val := by sorry
