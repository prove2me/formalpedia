-- Prove2me | Theorems.Thm_QuarterSumLadder_quarter_sum_expansion
-- name    : QuarterSumLadder.quarter_sum_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:36.65209+00:00
-- url     : https://prove2.me/theorems/e9feee05-43c4-44ba-8e30-5692dadbab1d
-- title:
--   Quarter Sum Ladder: quarter sum expansion
-- statement:
--   **The four-term expansion** (Paper IV, Lemma 5.1): with `z = i - 1`,
--   `Ω = Q + (R₁ + 2R₂ + 3R₃) z + (R₂ + 3R₃) z² + R₃ z³`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L94-L98
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L94-L98

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.quarter_sum_expansion {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    Omega χ = (Q p : GaussianInt) + ((R χ 1 + 2 * R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) +
      ((R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) ^ 2 +
        (R χ 3 : GaussianInt) * (gi - 1) ^ 3 := by sorry
