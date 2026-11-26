-- Prove2me | Theorems.Thm_QuarterSumLadder_E_eq
-- name    : QuarterSumLadder.E_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:02:34.993253+00:00
-- url     : https://prove2.me/theorems/607ad023-c84d-432a-be82-ad922b5f85e4
-- title:
--   Quarter Sum Ladder: E eq
-- statement:
--   `E_z` counts the odd elements in `(0, p/2)` of the class of `χ(2) z`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L236-L265
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean#L236-L265

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

theorem QuarterSumLadder.E_eq (z : GaussianInt) :
    E χ z = ((fiber χ (χ 2 * z)).filter fun x => 2 * x.val < p ∧ Odd x.val).card := by sorry
