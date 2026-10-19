-- Prove2me | Theorems.Thm_PermanentRollout_affine_restrictTotalDegree_finrank
-- name    : PermanentRollout.affine_restrictTotalDegree_finrank
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/9662d335-4327-4c5e-bb43-4d80863d8877
-- title:
--   PermanentRollout.affine_restrictTotalDegree_finrank
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.affine_restrictTotalDegree_finrank
    {ι : Type*} [Fintype ι] (N : ℕ) :
    Module.finrank ℂ (MvPolynomial.restrictTotalDegree ι ℂ N) =
      (N + Fintype.card ι).choose (Fintype.card ι) := by sorry
