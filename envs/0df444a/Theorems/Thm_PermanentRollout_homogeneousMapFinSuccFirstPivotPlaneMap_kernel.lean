-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapFinSuccFirstPivotPlaneMap_kernel
-- name    : PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_kernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/29dc3824-d701-4b92-9162-887421671fd7
-- title:
--   PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_kernel
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators

theorem PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_kernel
    {n : ℕ} (c : Fin (n + 1) → ℂ)
    (hc : c 0 ≠ 0) (u : Fin n → ℂ) :
    ∑ i : Fin (n + 1),
      c i * homogeneousMapFinSuccFirstPivotPlaneMap c u i = 0 := by sorry
