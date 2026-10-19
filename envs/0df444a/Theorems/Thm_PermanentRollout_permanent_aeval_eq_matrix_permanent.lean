-- Prove2me | Theorems.Thm_PermanentRollout_permanent_aeval_eq_matrix_permanent
-- name    : PermanentRollout.permanent_aeval_eq_matrix_permanent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/92d2dbb8-9b54-4f19-ab7f-579385ff8e58
-- title:
--   PermanentRollout.permanent_aeval_eq_matrix_permanent
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

theorem PermanentRollout.permanent_aeval_eq_matrix_permanent
    {n : ℕ} {ι : Type*}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ)) :
    MvPolynomial.aeval (fun ij : Fin n × Fin n => A ij.1 ij.2)
      (permanent n) = Matrix.permanent A := by sorry
