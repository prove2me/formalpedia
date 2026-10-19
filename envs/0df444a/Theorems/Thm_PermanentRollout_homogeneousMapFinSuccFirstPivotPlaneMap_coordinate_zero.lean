-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_zero
-- name    : PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/58dd71ad-33d9-4612-8bad-87dc5fa9a9ad
-- title:
--   PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_zero
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

theorem PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_zero
    {n : ℕ} (c : Fin (n + 1) → ℂ) :
    linearCoordinatePolynomial
      (homogeneousMapFinSuccFirstPivotPlaneMap c) 0 =
      homogeneousMapFinSuccFirstPivotPlaneRoot c := by sorry
