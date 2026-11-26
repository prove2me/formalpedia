-- Prove2me | Theorems.Thm_QuarterSumLadder_four_term_expansion
-- name    : QuarterSumLadder.four_term_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:05.345857+00:00
-- url     : https://prove2.me/theorems/b09c2195-4f01-5026-ab6a-3714d74c711f
-- title:
--   Quarter Sum Ladder: four term expansion
-- statement:
--   **The four-term expansion** (Paper IV, Lemma 5.1): with `z = i - 1`,
--   `Ω = Q + (R₁ + 2R₂ + 3R₃) z + (R₂ + 3R₃) z² + R₃ z³`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L37-L45
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L37-L45

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
public import Definitions.Def_QuarterSumLadder_Ladder
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.four_term_expansion :
    Omega χ = (Q p : GaussianInt) + ((R χ 1 + 2 * R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) +
      ((R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) ^ 2 +
        (R χ 3 : GaussianInt) * (gi - 1) ^ 3 := by sorry
