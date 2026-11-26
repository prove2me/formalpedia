-- Prove2me | Theorems.Thm_QuarterSumLadder_weight_two_comparison
-- name    : QuarterSumLadder.weight_two_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:18:01.27784+00:00
-- url     : https://prove2.me/theorems/42322f97-e107-4448-9d43-7d1389e97ae2
-- title:
--   Quarter Sum Ladder: weight two comparison
-- statement:
--   **The comparison lemma** (Paper IV, Lemma 8.1): `p(c₀ - c₁) ≡ -4(x - y) (mod 16)`. The paper
--   assumes `χ(2) = 1`; the congruence holds without it.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L162-L164
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L162-L164

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.weight_two_comparison {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (p : ℤ) * (c0 χ - c1 χ) ≡ -4 * ((Omega χ).re - (Omega χ).im) [ZMOD 16] := by sorry
