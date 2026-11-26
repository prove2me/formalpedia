-- Prove2me | Theorems.Thm_QuarterSumLadder_quartic_gauss_lemma
-- name    : QuarterSumLadder.quartic_gauss_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:56.286958+00:00
-- url     : https://prove2.me/theorems/e9f18aa7-cbbf-59a8-924a-8cd30a1f6238
-- title:
--   Quarter Sum Ladder: quartic gauss lemma
-- statement:
--   **The quartic Gauss lemma** (Williams–Currie; proof of Theorem 3.2): `2^Q = (-1)^{R₁ + R₃}` in
--   `ZMod p`, so `χ(2) = (-1)^{R₁ + R₃}`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L68-L70
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L68-L70

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.quartic_gauss_lemma {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (2 : ZMod p) ^ Q p = (-1) ^ (R χ 1 + R χ 3) ∧ χ 2 = (-1) ^ (R χ 1 + R χ 3) := by sorry
