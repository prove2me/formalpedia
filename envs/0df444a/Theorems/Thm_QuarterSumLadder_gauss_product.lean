-- Prove2me | Theorems.Thm_QuarterSumLadder_gauss_product
-- name    : QuarterSumLadder.gauss_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:02.391042+00:00
-- url     : https://prove2.me/theorems/171573d8-35c7-5e2b-a15e-92c4d598a400
-- title:
--   Quarter Sum Ladder: gauss product
-- statement:
--   **The Gauss–Lehmer product.**
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L63-L99
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean#L63-L99

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.gauss_product (hp2 : p ≠ 2) (A : Finset (ZMod p))
    (hA : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p) (hφ : ∀ x ∈ A, gaussMap x ∈ A) :
    (2 : ZMod p) ^ A.card * (-1) ^ (A.filter fun x => ¬ 4 * x.val < p).card = 1 := by sorry
