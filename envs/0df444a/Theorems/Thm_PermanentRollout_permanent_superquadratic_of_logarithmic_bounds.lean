-- Prove2me | Theorems.Thm_PermanentRollout_permanent_superquadratic_of_logarithmic_bounds
-- name    : PermanentRollout.permanent_superquadratic_of_logarithmic_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/0aaa4984-b805-48fa-86b1-78f6f911f413
-- title:
--   PermanentRollout.permanent_superquadratic_of_logarithmic_bounds
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.permanent_superquadratic_of_logarithmic_bounds
    (hbound : ∀ d : ℕ, 3 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤
        (circuitComplexity (permanent n) : ℝ)) :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (n : ℝ) ^ 2 ≤ (circuitComplexity (permanent n) : ℝ) := by sorry
