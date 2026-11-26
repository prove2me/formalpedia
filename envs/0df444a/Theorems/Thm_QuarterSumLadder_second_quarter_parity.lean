-- Prove2me | Theorems.Thm_QuarterSumLadder_second_quarter_parity
-- name    : QuarterSumLadder.second_quarter_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:30.12237+00:00
-- url     : https://prove2.me/theorems/b45c6ca5-8962-5349-a603-c51552f6a7ea
-- title:
--   Quarter Sum Ladder: second quarter parity
-- statement:
--   **The parity of `R₂`** (proof of Theorem 5.4): if `χ(2) = 1`, then
--   `R₂ ≡ (p - 1)/8 + [2^{(p-1)/8} = -1] (mod 2)`, and `[2^{(p-1)/8} = -1] ≡ [2 ∣ ρ] (p - 1)/(4ρ) (mod 2)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L136-L140
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L136-L140

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.second_quarter_parity {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1) :
    R χ 2 % 2 = ((p - 1) / 8 + if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 ∧
      (if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 =
        (if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0) % 2 := by sorry
