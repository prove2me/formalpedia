-- Prove2me | Theorems.Thm_QuarterSumLadder_two_ne_zero_zmod
-- name    : QuarterSumLadder.two_ne_zero_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:42.283884+00:00
-- url     : https://prove2.me/theorems/e103e608-9670-5b97-bdcf-9e7c9180a029
-- title:
--   Quarter Sum Ladder: two ne zero zmod
-- statement:
--   The Quarter Sum Ladder construction uses the two ne zero zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L30-L34
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L30-L34

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by sorry
