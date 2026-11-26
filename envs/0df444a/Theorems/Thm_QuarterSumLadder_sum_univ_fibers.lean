-- Prove2me | Theorems.Thm_QuarterSumLadder_sum_univ_fibers
-- name    : QuarterSumLadder.sum_univ_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:01:21.812012+00:00
-- url     : https://prove2.me/theorems/b7dcdffa-5fb8-4072-b7e7-ed3259d69a91
-- title:
--   Quarter Sum Ladder: sum univ fibers
-- statement:
--   A sum over `ZMod p` of a function vanishing at `0` splits over the four classes.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L87-L104
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L87-L104

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8

theorem QuarterSumLadder.sum_univ_fibers {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (h0 : f 0 = 0) :
    ∑ x, f x = ∑ x ∈ fiber χ 1, f x + ∑ x ∈ fiber χ gi, f x + ∑ x ∈ fiber χ (-1), f x +
      ∑ x ∈ fiber χ (-gi), f x := by sorry
