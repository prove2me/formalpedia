-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_source_coordinate
-- name    : PermanentRollout.homogeneousMap_allTarget_rees_source_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/58b05897-31f5-44e3-9c9a-552ef39f40b4
-- title:
--   PermanentRollout.homogeneousMap_allTarget_rees_source_coordinate
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
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators
open scoped Pointwise
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousMap_allTarget_rees_source_coordinate
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (i : Fin k) :
    homogeneousMapAllTargetReesSourceRingHom F target e
      (⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ :
        homogeneousMapSubalgebra F) =
      homogeneousMapAllTargetReesParameterRingHom F target e
        (Polynomial.C (target i) * Polynomial.X ^ e) := by sorry
