-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_isHomogeneous_mw_6c8ae1086a4a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_isHomogeneous_mw_6c8ae1086a4a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:06.713086+00:00
-- url     : https://prove2.me/theorems/afe98e6a-b04d-4ef9-95ca-5c76e81aa0d9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Scaling Indep is Homogeneous mw 6c8ae1086a4a: P2 M Ground Theory Heights  Heights Inter Chart Scaling Indep is Homogeneous mw 6c8ae1086a4a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Scaling Indep is Homogeneous mw 6c8ae1086a4a construction uses the P2 M Ground Theory Heights  Heights Inter Chart Scaling Indep is Homogeneous mw 6c8ae1086a4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartScalingIndep.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartScalingIndep.lean#L19-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartScalingIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_isHomogeneous_mw_6c8ae1086a4a {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartScalingIndep».«isHomogeneous_mw» := P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_isHomogeneous_mw_6c8ae1086a4a
