-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_parameterFiber_finrank
-- name    : PermanentRollout.homogeneousMap_allTarget_rees_parameterFiber_finrank
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/c2b3c5bd-4af7-4635-bc69-ef5d3195f744
-- title:
--   PermanentRollout.homogeneousMap_allTarget_rees_parameterFiber_finrank
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
open scoped TensorProduct

theorem PermanentRollout.homogeneousMap_allTarget_rees_parameterFiber_finrank
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (hfinite :
      letI : Algebra (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e) :=
          homogeneousMapAllTargetReesParameterAlgebra F target e
      Module.Finite (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e))
    (a : ℂ) :
    letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
        homogeneousMapAllTargetReesParameterAlgebra F target e
    Module.finrank ℂ
      (homogeneousMapAllTargetReesQuotient F target e ⧸
        (RingHom.ker (Polynomial.aeval a).toRingHom).map
          (algebraMap (Polynomial ℂ)
            (homogeneousMapAllTargetReesQuotient F target e))) =
      Module.finrank (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e) := by sorry
