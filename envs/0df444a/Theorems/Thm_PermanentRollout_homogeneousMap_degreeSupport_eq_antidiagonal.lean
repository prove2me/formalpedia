-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_degreeSupport_eq_antidiagonal
-- name    : PermanentRollout.homogeneousMap_degreeSupport_eq_antidiagonal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/54a06e29-8933-4190-aca5-faf8f70eceae
-- title:
--   PermanentRollout.homogeneousMap_degreeSupport_eq_antidiagonal
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

theorem PermanentRollout.homogeneousMap_degreeSupport_eq_antidiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    {d : ι →₀ ℕ | d.degree = n} =
      (((Finset.univ : Finset ι).finsuppAntidiag n : Finset (ι →₀ ℕ)) :
        Set (ι →₀ ℕ)) := by sorry
