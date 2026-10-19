-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_exists_coordinateSubset_independent_linear_origin_slices
-- name    : PermanentRollout.homogeneousMap_exists_coordinateSubset_independent_linear_origin_slices
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/4ec81973-501b-405b-9171-cad93def5fc3
-- title:
--   PermanentRollout.homogeneousMap_exists_coordinateSubset_independent_linear_origin_slices
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

theorem PermanentRollout.homogeneousMap_exists_coordinateSubset_independent_linear_origin_slices
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (coordinates : Finset (Fin k)) :
    ∃ c : Fin (k - coordinates.card) → Fin k → ℂ,
      LinearIndependent ℂ c ∧
      MvPolynomial.zeroLocus ℂ
        (homogeneousLinearSliceIdeal
          (Ideal.span (F '' (coordinates : Set (Fin k)))) c) =
        ({0} : Set (Fin k → ℂ)) := by sorry
