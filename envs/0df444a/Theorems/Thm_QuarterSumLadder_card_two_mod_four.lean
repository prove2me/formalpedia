-- Prove2me | Theorems.Thm_QuarterSumLadder_card_two_mod_four
-- name    : QuarterSumLadder.card_two_mod_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:08:20.393634+00:00
-- url     : https://prove2.me/theorems/06dac87c-e9fb-5384-be26-01c522130fa0
-- title:
--   Quarter Sum Ladder: card two mod four
-- statement:
--   `#{0 < m < p : m ≡ 2 (mod 4)} = Q`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L39-L58
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L39-L58

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.card_two_mod_four (hp8 : p % 8 = 1) :
    (univ.filter fun x : ZMod p => x.val % 4 = 2).card = Q p := by sorry
