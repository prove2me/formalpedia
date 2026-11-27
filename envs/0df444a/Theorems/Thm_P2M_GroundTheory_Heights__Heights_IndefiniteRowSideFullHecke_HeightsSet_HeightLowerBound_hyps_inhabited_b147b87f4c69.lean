-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightLowerBound_hyps_inhabited_b147b87f4c69
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightLowerBound_hyps_inhabited_b147b87f4c69
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:23:52.239698+00:00
-- url     : https://prove2.me/theorems/3e18627f-0c50-5be9-966c-dc31be185864
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Height Lower Bound hyps inhabited b147b87f4c69: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Height
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Height Lower Bound hyps inhabited b147b87f4c69 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set Height Lower Bound hyps inhabited b147b87f4c69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSaturatedFirstCoordinateLine.lean#L239-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSaturatedFirstCoordinateLine.lean#L239-L248

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightLowerBound_hyps_inhabited_b147b87f4c69 :
    IsSmoothHerm (fsLine 1) ∧ (∀ j, ![(1 : ℚ)] j ∈ chartLat yPt (fsLine 1).a 1) ∧
      (∀ j, IsSectionBounded (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1) (![(1 : ℚ)] j)
        (Real.exp 0)) ∧
      NoCommonZero (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1).a ![(1 : ℚ)] ∧
      IsArithVar (mCoordIdeal (ι := PBlk 1) yPt) 1 ∧
      mCoordIdeal (ι := PBlk 1) yPt ≤ mCoordIdeal (ι := PBlk 1) yPt := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«HeightLowerBound».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightLowerBound_hyps_inhabited_b147b87f4c69
