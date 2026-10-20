-- Prove2me | Theorems.Thm_SoficGroups_diagonalRadius_error_tendsto_zero
-- name    : SoficGroups.diagonalRadius_error_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/10672121-d268-4c6f-ad83-b39825a975bf
-- title:
--   SoficGroups.diagonalRadius_error_tendsto_zero
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

theorem SoficGroups.diagonalRadius_error_tendsto_zero (e : ℕ → ℕ → ℝ)
    (hnonneg : ∀ n k, 0 ≤ e n k)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    Tendsto (fun n => e n (diagonalRadius e n)) atTop (𝓝 0) := by sorry
