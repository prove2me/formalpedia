-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralProjIndep_proof_944cefc4c00d
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralProjIndep_proof_944cefc4c00d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:13.449116+00:00
-- url     : https://prove2.me/theorems/e8d2a645-d47a-45e1-b529-deb6b520b358
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Proj Indep proof 944cefc4c00d: P2 M Ground Theory Heights  Heights Pts Integral Proj Indep proof 944cefc4c00d
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Proj Indep proof 944cefc4c00d construction uses the P2 M Ground Theory Heights  Heights Pts Integral Proj Indep proof 944cefc4c00d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsIntegralProjIndep.lean#L37-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsIntegralProjIndep.lean#L37-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsIntegralProjIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartProjIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsIntegralProjIndep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero

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
open MeasureTheory Filter
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegralAt sheetDensity
  fibre pot mcPts fibreFinite isOpen_blockNonzero)

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralProjIndep_proof_944cefc4c00d (hInt : PtsPosDensIntegrable.Statement)
    (hPos : PtsPosPartProjIndep.Statement) : PtsIntegralProjIndep.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralProjIndep».«proof» := P2M_GroundTheory_Heights__Heights_PtsIntegralProjIndep_proof_944cefc4c00d
