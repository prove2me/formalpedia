-- Prove2me | Theorems.Thm_SoficGroups_cubeSum_le_dominant_mul_sum
-- name    : SoficGroups.cubeSum_le_dominant_mul_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/6414ce65-cbbc-40d9-a6e9-5e6dc7a55195
-- title:
--   SoficGroups.cubeSum_le_dominant_mul_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.cubeSum_le_dominant_mul_sum (ps : List ℝ) (m : ℝ)
    (hpos : ∀ p ∈ ps, 0 ≤ p)
    (hone : ∀ p ∈ ps, p ≤ 1)
    (hdom : ∀ p ∈ ps, p ≤ m) :
    (ps.map fun p => p ^ 3).sum ≤ m * ps.sum := by sorry
