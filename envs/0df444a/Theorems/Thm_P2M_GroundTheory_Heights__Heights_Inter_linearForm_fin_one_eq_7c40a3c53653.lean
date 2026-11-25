-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_linearForm_fin_one_eq_7c40a3c53653
-- name    : P2M_GroundTheory_Heights__Heights_Inter_linearForm_fin_one_eq_7c40a3c53653
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:05.682632+00:00
-- url     : https://prove2.me/theorems/42753bb5-907a-4a50-8908-00d21b4d9bc5
-- title:
--   P2 M Ground Theory Heights  Heights Inter linear Form fin one eq 7c40a3c53653: P2 M Ground Theory Heights  Heights Inter linear Form fin one eq 7c40a3c53653
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter linear Form fin one eq 7c40a3c53653 construction uses the P2 M Ground Theory Heights  Heights Inter linear Form fin one eq 7c40a3c53653 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHomogeneousOfIsMultiHomogOne.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHomogeneousOfIsMultiHomogOne.lean#L19-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLineFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLinearQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHomogeneousOfIsMultiHomogOne
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
variable {F : Type} [Field F]

theorem P2M_GroundTheory_Heights__Heights_Inter_linearForm_fin_one_eq_7c40a3c53653 {g : MvPolynomial (Fin 1) F} (hg : g.IsHomogeneous 1) :
    g = C (coeff (Finsupp.single 0 1) g) * X 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«linearForm_fin_one_eq» := P2M_GroundTheory_Heights__Heights_Inter_linearForm_fin_one_eq_7c40a3c53653
