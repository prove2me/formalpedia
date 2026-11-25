-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightPullback_hyps_inhabited_8578ee2ba7ab
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightPullback_hyps_inhabited_8578ee2ba7ab
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:24:00.794128+00:00
-- url     : https://prove2.me/theorems/5294141f-b0ed-58e3-a329-ce53e2f00984
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Height Pullback hyps inhabited 8578ee2ba7ab: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Height Pullback hyps inhabited 8578ee2ba7ab construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Height Pullback hyps inhabited 8578ee2ba7ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSaturatedFirstCoordinateLine.lean#L266-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSaturatedFirstCoordinateLine.lean#L266-L280

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DegreeGeneric_hyps_inhabited_36d80aab7c4b

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open NumberField

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightPullback_hyps_inhabited_8578ee2ba7ab :
    IsBlockMap (ι := PBlk 1) (ι' := PBlk 1) id id ∧ IsArithVar (mCoordIdeal (ι := PBlk 1) yPt) 1 ∧
      IsArithVar (imageZ (ι := PBlk 1) (ι' := PBlk 1) id (mCoordIdeal yPt)) 1 ∧
      IsSmoothHerm (fsLine 1) ∧ IsPullHerm (ι := PBlk 1) (ι' := PBlk 1) id id (fsLine 1) (fsLine 1) ∧
      IntermediateField.relfinrank (blockFnField (yPt ∘ id)) (blockFnField yPt) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«HeightPullback».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightPullback_hyps_inhabited_8578ee2ba7ab
