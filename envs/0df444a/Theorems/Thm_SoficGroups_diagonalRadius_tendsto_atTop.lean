-- Prove2me | Theorems.Thm_SoficGroups_diagonalRadius_tendsto_atTop
-- name    : SoficGroups.diagonalRadius_tendsto_atTop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/34b1a02c-5e33-4390-86a2-ab9d49b8bb48
-- title:
--   SoficGroups.diagonalRadius_tendsto_atTop
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

theorem SoficGroups.diagonalRadius_tendsto_atTop (e : ℕ → ℕ → ℝ)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    Tendsto (diagonalRadius e) atTop atTop := by sorry
