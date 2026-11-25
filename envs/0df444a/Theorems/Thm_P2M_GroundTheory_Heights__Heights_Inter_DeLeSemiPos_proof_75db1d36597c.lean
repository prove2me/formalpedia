-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DeLeSemiPos_proof_75db1d36597c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DeLeSemiPos_proof_75db1d36597c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:31:59.396154+00:00
-- url     : https://prove2.me/theorems/98512ba3-bb98-575d-9d9a-e447a05cd096
-- title:
--   P2 M Ground Theory Heights  Heights Inter De Le Semi Pos proof 75db1d36597c: P2 M Ground Theory Heights  Heights Inter De Le Semi Pos proof 75db1d36597c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter De Le Semi Pos proof 75db1d36597c construction uses the P2 M Ground Theory Heights  Heights Inter De Le Semi Pos proof 75db1d36597c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeLeSemiPos.lean#L79-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeLeSemiPos.lean#L79-L188

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DeLeSemiPos_proof_75db1d36597c (hPL1 : ArithmeticPoincareLelongFormula) (hSt : StokesStatement) (hAdd : PtsAddFirst.Statement)
    (hLim : PtsRegLimit.Statement) (hMono : PtsMonoSemiPos.Statement) (hCurv : RegCurvBound.Statement)
    (hNot : HorizNotMem.Statement) : DeLeSemiPos.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DeLeSemiPos».«proof» := P2M_GroundTheory_Heights__Heights_Inter_DeLeSemiPos_proof_75db1d36597c
