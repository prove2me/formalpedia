-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_finsum_le_finsum_abs_200e865e6b5f
-- name    : P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_finsum_le_finsum_abs_200e865e6b5f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:56:09.834919+00:00
-- url     : https://prove2.me/theorems/07cab966-754e-58c5-8cd7-e525d4716e48
-- title:
--   P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite finsum le finsum abs 200e865e6b5f: P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite finsum le finsum abs 200e865e6b5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite finsum le finsum abs 200e865e6b5f construction uses the P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite finsum le finsum abs 200e865e6b5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSemiPosMassFinite.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSemiPosMassFinite.lean#L21-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSemiPosMassFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSegreChartFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartProjFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSheetHessPSD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSemiPosMassFinite
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
open MeasureTheory
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot sheetDensity fibre mcPts segre
  maDensity cxHessian IsSheet)
open GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite

theorem P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_finsum_le_finsum_abs_200e865e6b5f {α : Type*} (G : α → ℝ) : ∑ᶠ x, G x ≤ ∑ᶠ x, |G x| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSemiPosMassFinite».«finsum_le_finsum_abs» := P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_finsum_le_finsum_abs_200e865e6b5f
