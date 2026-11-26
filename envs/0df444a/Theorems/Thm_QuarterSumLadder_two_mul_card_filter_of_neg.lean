-- Prove2me | Theorems.Thm_QuarterSumLadder_two_mul_card_filter_of_neg
-- name    : QuarterSumLadder.two_mul_card_filter_of_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:08.992416+00:00
-- url     : https://prove2.me/theorems/110bf1bf-1d7f-421e-b3e6-aeebedd55e01
-- title:
--   Quarter Sum Ladder: two mul card filter of neg
-- statement:
--   A set closed under negation, not containing `0`, is split in half by any predicate that
--   negation reverses.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L38-L52
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L38-L52

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.two_mul_card_filter_of_neg {S : Finset (ZMod p)} (P : ZMod p → Prop) [DecidablePred P]
    (hS : ∀ x ∈ S, -x ∈ S) (hP : ∀ x ∈ S, (P (-x) ↔ ¬ P x)) :
    2 * (S.filter P).card = S.card := by sorry
