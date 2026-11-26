-- Prove2me | Theorems.Thm_QuarterSumLadder_ladder_fourth
-- name    : QuarterSumLadder.ladder_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:32.397025+00:00
-- url     : https://prove2.me/theorems/d37acc39-13a8-5d72-99f4-5f1d3f5e52d0
-- title:
--   Quarter Sum Ladder: ladder fourth
-- statement:
--   **The fourth threshold** (Paper IV, Theorem 5.3): if `χ(2) = 1` and `p ≡ 1 (mod 16)`, then
--   `16 ∣ N(Ω) ⟺ R₁ + 2R₂ + R₃ ≡ 0 (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L117-L120
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L117-L120

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.ladder_fourth {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1)
    (h16 : p % 16 = 1) :
    (16 : ℤ) ∣ (Omega χ).norm ↔ (R χ 1 + 2 * R χ 2 + R χ 3) % 4 = 0 := by sorry
