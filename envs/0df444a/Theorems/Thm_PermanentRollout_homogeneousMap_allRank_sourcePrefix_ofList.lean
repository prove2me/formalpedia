-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_sourcePrefix_ofList
-- name    : PermanentRollout.homogeneousMap_allRank_sourcePrefix_ofList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/d794b8a6-3cdd-47ec-aa67-6ac39836c3ce
-- title:
--   PermanentRollout.homogeneousMap_allRank_sourcePrefix_ofList
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

theorem PermanentRollout.homogeneousMap_allRank_sourcePrefix_ofList
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (j : ℕ) :
    Ideal.ofList ((List.ofFn F).take j) =
      Ideal.span (F ''
        (homogeneousMapAllKSourcePrefix k j : Set (Fin k))) := by sorry
