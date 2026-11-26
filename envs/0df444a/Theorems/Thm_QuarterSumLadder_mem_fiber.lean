-- Prove2me | Theorems.Thm_QuarterSumLadder_mem_fiber
-- name    : QuarterSumLadder.mem_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:59:30.344798+00:00
-- url     : https://prove2.me/theorems/64acf61a-3779-5bab-9429-721bc359df30
-- title:
--   Quarter Sum Ladder: mem fiber
-- statement:
--   The Quarter Sum Ladder construction uses the mem fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L33-L34
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L33-L34

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.mem_fiber {χ : MulChar (ZMod p) GaussianInt} {x : ZMod p} {z : GaussianInt} :
    x ∈ fiber χ z ↔ χ x = z := by sorry
