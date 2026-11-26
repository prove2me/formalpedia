-- Prove2me | Theorems.Thm_P2M_QuarterSumLadder_val_neg_of_ne_zero__948b4628a7e3
-- name    : P2M_QuarterSumLadder_val_neg_of_ne_zero__948b4628a7e3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:54.700875+00:00
-- url     : https://prove2.me/theorems/1d51e117-052b-459a-aea9-2c36fd83987d
-- title:
--   P2 M Quarter Sum Ladder val neg of ne zero  948b4628a7e3: P2 M Quarter Sum Ladder val neg of ne zero  948b4628a7e3
-- statement:
--   The P2 M Quarter Sum Ladder val neg of ne zero  948b4628a7e3 construction uses the P2 M Quarter Sum Ladder val neg of ne zero  948b4628a7e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L24-L25
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L24-L25

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_QuarterSumLadder_val_neg_of_ne_zero__948b4628a7e3 {x : ZMod p} (hx : x ≠ 0) : (-x).val = p - x.val := by sorry

alias «QuarterSumLadder».«val_neg_of_ne_zero'» := P2M_QuarterSumLadder_val_neg_of_ne_zero__948b4628a7e3
