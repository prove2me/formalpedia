-- Prove2me | Theorems.Thm_P2M_centeredNumericalRadiusMinimizers_unitary_conjugate__c5459a6166b7
-- name    : P2M_centeredNumericalRadiusMinimizers_unitary_conjugate__c5459a6166b7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:08:28.507925+00:00
-- url     : https://prove2.me/theorems/e01abe4d-fd5b-4747-8336-93af9557bcfa
-- title:
--   P2 M centered Numerical Radius Minimizers unitary conjugate  c5459a6166b7: P2 M centered Numerical Radius Minimizers unitary conjugate  c5459a6166b7
-- statement:
--   The alternate orientation of unitary conjugation also preserves every
--   optimal scalar center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L423-L429
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/RadiusAffine.lean#L423-L429

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E]

theorem P2M_centeredNumericalRadiusMinimizers_unitary_conjugate__c5459a6166b7 [CompleteSpace E]
    (A U : E →L[ℂ] E) (hU : U ∈ unitary (E →L[ℂ] E)) :
    centeredNumericalRadiusMinimizers (U * A * U†) =
      centeredNumericalRadiusMinimizers A := by sorry

alias «centeredNumericalRadiusMinimizers_unitary_conjugate'» := P2M_centeredNumericalRadiusMinimizers_unitary_conjugate__c5459a6166b7
