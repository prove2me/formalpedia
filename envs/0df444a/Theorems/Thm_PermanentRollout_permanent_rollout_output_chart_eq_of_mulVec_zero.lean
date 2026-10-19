-- Prove2me | Theorems.Thm_PermanentRollout_permanent_rollout_output_chart_eq_of_mulVec_zero
-- name    : PermanentRollout.permanent_rollout_output_chart_eq_of_mulVec_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/07abd40f-38b3-45c3-b03e-4e143a1c6b9a
-- title:
--   PermanentRollout.permanent_rollout_output_chart_eq_of_mulVec_zero
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

theorem PermanentRollout.permanent_rollout_output_chart_eq_of_mulVec_zero
    {k m : ℕ}
    (g : (Fin (k + 1) → ℂ) → (Fin (m + 1) → ℂ))
    (j : Fin (k + 1)) (ell : Fin (m + 1))
    (w : Fin (k + 1) → ℂ) (hwj : w j = 1)
    (hell : g w ell ≠ 0)
    (A : Matrix (Fin (k + 1)) (Fin (m + 1)) ℂ)
    (hA : Matrix.mulVec A (g w) = 0) :
    permanentRolloutOutputChart g j ell
        (j.removeNth w,
          fun r q => A r (ell.succAbove q)) = A := by sorry
