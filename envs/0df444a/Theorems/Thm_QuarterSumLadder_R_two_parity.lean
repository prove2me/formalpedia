-- Prove2me | Theorems.Thm_QuarterSumLadder_R_two_parity
-- name    : QuarterSumLadder.R_two_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:07:26.35803+00:00
-- url     : https://prove2.me/theorems/c28fa327-7a97-5c61-a18b-28580d7dcd7e
-- title:
--   Quarter Sum Ladder: R two parity
-- statement:
--   The parity of `R₂` when `χ(2) = 1`: `R₂ ≡ (p - 1)/8 + [2^{(p-1)/8} = -1] (mod 2)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L249-L265
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L249-L265

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.R_two_parity (hw : χ 2 = 1) :
    R χ 2 % 2 = ((p - 1) / 8 + if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 := by sorry
