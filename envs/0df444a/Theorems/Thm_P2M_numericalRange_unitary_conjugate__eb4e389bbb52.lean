-- Prove2me | Theorems.Thm_P2M_numericalRange_unitary_conjugate__eb4e389bbb52
-- name    : P2M_numericalRange_unitary_conjugate__eb4e389bbb52
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:41.133006+00:00
-- url     : https://prove2.me/theorems/f11b4602-55fd-49dc-af26-e96548d69913
-- title:
--   P2 M numerical Range unitary conjugate  eb4e389bbb52: P2 M numerical Range unitary conjugate  eb4e389bbb52
-- statement:
--   The alternate orientation of unitary conjugation also preserves the
--   numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L58-L62
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAdjoint.lean#L58-L62

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem P2M_numericalRange_unitary_conjugate__eb4e389bbb52 (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRange (U * A * U†) = numericalRange A := by sorry

alias «numericalRange_unitary_conjugate'» := P2M_numericalRange_unitary_conjugate__eb4e389bbb52
