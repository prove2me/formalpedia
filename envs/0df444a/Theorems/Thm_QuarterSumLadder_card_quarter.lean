-- Prove2me | Theorems.Thm_QuarterSumLadder_card_quarter
-- name    : QuarterSumLadder.card_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:06:36.595801+00:00
-- url     : https://prove2.me/theorems/edb9ea3d-c529-48bf-ac41-b6ffde121978
-- title:
--   Quarter Sum Ladder: card quarter
-- statement:
--   `#{x : x ≠ 0, ⟨x⟩ < p/4} = Q`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L30-L48
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L30-L48

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.card_quarter (hp8 : p % 8 = 1) :
    (univ.filter fun x : ZMod p => x ≠ 0 ∧ 4 * x.val < p).card = Q p := by sorry
