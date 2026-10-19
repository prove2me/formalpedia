-- Prove2me | Theorems.Thm_SoficGroups_exists_diverging_radius_with_vanishing_diagonal_error
-- name    : SoficGroups.exists_diverging_radius_with_vanishing_diagonal_error
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/c9b0e259-442a-4e14-88ff-3b459aca9876
-- title:
--   SoficGroups.exists_diverging_radius_with_vanishing_diagonal_error
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

theorem SoficGroups.exists_diverging_radius_with_vanishing_diagonal_error
    (e : ℕ → ℕ → ℝ) (hnonneg : ∀ n k, 0 ≤ e n k)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∃ r : ℕ → ℕ,
      Tendsto r atTop atTop ∧
        Tendsto (fun n => e n (r n)) atTop (𝓝 0) := by sorry
