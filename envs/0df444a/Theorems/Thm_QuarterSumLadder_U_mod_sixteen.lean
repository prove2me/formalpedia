-- Prove2me | Theorems.Thm_QuarterSumLadder_U_mod_sixteen
-- name    : QuarterSumLadder.U_mod_sixteen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:20.221435+00:00
-- url     : https://prove2.me/theorems/b5a348b5-ad42-51dc-8cb1-6fdf35399e0c
-- title:
--   Quarter Sum Ladder: U mod sixteen
-- statement:
--   `U_z ≡ #(odd) + 8 #(≡ ±3 mod 8) + 4 E_z (mod 16)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L62-L69
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L62-L69

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8 hχ

theorem QuarterSumLadder.U_mod_sixteen (z : GaussianInt) :
    ((U χ z : ℤ) : ZMod 16) =
      (((fiber χ z).filter fun x => x.val % 2 = 1).card : ZMod 16) +
        8 * (((fiber χ z).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card : ZMod 16) +
          4 * (E χ z : ZMod 16) := by sorry
