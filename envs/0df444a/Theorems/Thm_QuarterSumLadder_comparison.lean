-- Prove2me | Theorems.Thm_QuarterSumLadder_comparison
-- name    : QuarterSumLadder.comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:30.946449+00:00
-- url     : https://prove2.me/theorems/6a54e603-9ee8-5477-82cb-b1438379f305
-- title:
--   Quarter Sum Ladder: comparison
-- statement:
--   **The comparison lemma** (Paper IV, Lemma 8.1).
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L72-L129
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L72-L129

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

theorem QuarterSumLadder.comparison :
    (p : ℤ) * (c0 χ - c1 χ) ≡ -4 * ((Omega χ).re - (Omega χ).im) [ZMOD 16] := by sorry
