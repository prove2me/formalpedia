-- Prove2me | Theorems.Thm_SpherePacking_weighted_gram_sum_eq_norm_sq
-- name    : SpherePacking.weighted_gram_sum_eq_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:35.827193+00:00
-- url     : https://prove2.me/theorems/3ab0ecab-25c3-44c1-ae45-e8c28b7fc710
-- title:
--   SpherePacking.weighted_gram_sum_eq_norm_sq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace

theorem SpherePacking.weighted_gram_sum_eq_norm_sq {α E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Finset α) (w : α → ℝ) (v : α → E) :
    (∑ x ∈ C, ∑ y ∈ C, w x * w y * ⟪v x, v y⟫_ℝ) =
      ‖∑ x ∈ C, w x • v x‖ ^ 2 := by sorry
