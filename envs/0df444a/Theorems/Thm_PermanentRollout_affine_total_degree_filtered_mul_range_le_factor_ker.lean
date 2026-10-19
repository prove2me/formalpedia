-- Prove2me | Theorems.Thm_PermanentRollout_affine_total_degree_filtered_mul_range_le_factor_ker
-- name    : PermanentRollout.affine_total_degree_filtered_mul_range_le_factor_ker
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/daa389fa-d6ee-4bf9-a786-4ca5513ef98a
-- title:
--   PermanentRollout.affine_total_degree_filtered_mul_range_le_factor_ker
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

theorem PermanentRollout.affine_total_degree_filtered_mul_range_le_factor_ker
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (g : MvPolynomial ι ℂ) (n : ℕ) :
    (affineTotalDegreeFilteredMul I g n).range ≤
      (affineTotalDegreeFilteredFactor
        (show I ≤ I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)) from
          le_sup_left)
        (g.totalDegree + n)).ker := by sorry
