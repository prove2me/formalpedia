-- Prove2me | Theorems.Thm_P2M_numericalRadius_unitary_conjugate__32a47c7bb1cf
-- name    : P2M_numericalRadius_unitary_conjugate__32a47c7bb1cf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:07:39.749397+00:00
-- url     : https://prove2.me/theorems/a548ca51-be35-5f9d-8bbf-d9ee85a7400a
-- title:
--   P2 M numerical Radius unitary conjugate  32a47c7bb1cf: P2 M numerical Radius unitary conjugate  32a47c7bb1cf
-- statement:
--   Numerical radius is invariant under the alternate orientation of unitary
--   conjugation.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L73-L77
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L73-L77

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem P2M_numericalRadius_unitary_conjugate__32a47c7bb1cf (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRadius (U * A * U†) = numericalRadius A := by sorry

alias «numericalRadius_unitary_conjugate'» := P2M_numericalRadius_unitary_conjugate__32a47c7bb1cf
