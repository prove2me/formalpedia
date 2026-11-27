-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartProjIndep_proof_b20fbf74e715
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosPartProjIndep_proof_b20fbf74e715
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:10.61241+00:00
-- url     : https://prove2.me/theorems/71090541-4204-5fb8-8f50-e7dbab9750e6
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Part Proj Indep proof b20fbf74e715: P2 M Ground Theory Heights  Heights Pts Pos Part Proj Indep proof b20fbf74e715
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Part Proj Indep proof b20fbf74e715 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Part Proj Indep proof b20fbf74e715 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartProjIndep.lean#L45-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartProjIndep.lean#L45-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartProjIndep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre fibre IsSheet sheetDensity
  pot fibreFinite)

theorem P2M_GroundTheory_Heights__Heights_PtsPosPartProjIndep_proof_b20fbf74e715 (hS : PtsSheetSimpleNull.Statement) (hO : PtsSheetOnlyNull.Statement)
    (hL : PtsPosPartLocal.Statement) (hM : PtsPosDensMeasurable.Statement) :
    PtsPosPartProjIndep.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosPartProjIndep».«proof» := P2M_GroundTheory_Heights__Heights_PtsPosPartProjIndep_proof_b20fbf74e715
