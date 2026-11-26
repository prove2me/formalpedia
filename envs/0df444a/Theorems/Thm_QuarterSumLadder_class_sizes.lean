-- Prove2me | Theorems.Thm_QuarterSumLadder_class_sizes
-- name    : QuarterSumLadder.class_sizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:46.862944+00:00
-- url     : https://prove2.me/theorems/9f90c78f-2420-5cc8-ab84-61fc8a11cc43
-- title:
--   Quarter Sum Ladder: class sizes
-- statement:
--   Each class `D_z` (`z ∈ {1, i, -1, -i}`) has `Q = (p - 1)/4` elements, and `R₀ + R₁ + R₂ + R₃ = Q`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L31-L34
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L31-L34

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.class_sizes {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) {z : GaussianInt}
    (hz : (z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi)) :
    (fiber χ z).card = Q p ∧ R χ 0 + R χ 1 + R χ 2 + R χ 3 = Q p := by sorry
