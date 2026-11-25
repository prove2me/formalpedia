-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_one_8921dcb39a7e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_one_8921dcb39a7e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:16:43.423593+00:00
-- url     : https://prove2.me/theorems/f56af09b-a222-4bb7-8513-043d2c05faf0
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Section On one 8921dcb39a7e: P2 M Ground Theory Heights  Heights Inter is Section On one 8921dcb39a7e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Section On one 8921dcb39a7e construction uses the P2 M Ground Theory Heights  Heights Inter is Section On one 8921dcb39a7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeLeSemiPos.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeLeSemiPos.lean#L50-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsMonoSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRegCurvBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSectionOn_one

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_one_8921dcb39a7e {Q : Ideal (MRing ι)} {d : ℕ} (hQ : IsArithVar Q d) {D : HermLine ι}
    (hDa : D.a = 0) : IsSectionOn Q D 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isSectionOn_one» := P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_one_8921dcb39a7e
