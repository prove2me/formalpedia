-- Prove2me | Theorems.Thm_PermanentRollout_permanent_rollout_exists_output_matrix_of_smooth_homogeneous
-- name    : PermanentRollout.permanent_rollout_exists_output_matrix_of_smooth_homogeneous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/c28ab437-084d-400d-8b20-88234d3fad14
-- title:
--   PermanentRollout.permanent_rollout_exists_output_matrix_of_smooth_homogeneous
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section

theorem PermanentRollout.permanent_rollout_exists_output_matrix_of_smooth_homogeneous
    {k m e : ℕ}
    (g : (Fin k → ℂ) → (Fin m → ℂ))
    (hg : ContDiff ℝ 1 g)
    (hnonzero : ∀ u : Fin k → ℂ, u ≠ 0 → g u ≠ 0)
    (hscale : ∀ (a : ℂ) (u : Fin k → ℂ),
      g (a • u) = a ^ e • g u) :
    ∃ A : Matrix (Fin k) (Fin m) ℂ,
      ∀ u : Fin k → ℂ, u ≠ 0 → Matrix.mulVec A (g u) ≠ 0 := by sorry
