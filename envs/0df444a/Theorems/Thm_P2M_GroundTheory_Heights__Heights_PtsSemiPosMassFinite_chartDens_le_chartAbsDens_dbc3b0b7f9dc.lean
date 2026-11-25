-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_chartDens_le_chartAbsDens_dbc3b0b7f9dc
-- name    : P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_chartDens_le_chartAbsDens_dbc3b0b7f9dc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:32.275199+00:00
-- url     : https://prove2.me/theorems/b5e198e7-5a1b-541a-a5e9-27076726ca92
-- title:
--   P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite chart Dens le chart Abs Dens dbc3b0b7f9dc: P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite chart Dens le chart Abs Dens dbc3b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite chart Dens le chart Abs Dens dbc3b0b7f9dc construction uses the P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite chart Dens le chart Abs Dens dbc3b0b7f9dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSemiPosMassFinite.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSemiPosMassFinite.lean#L31-L38

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

theorem P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_chartDens_le_chartAbsDens_dbc3b0b7f9dc {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartDens J A f φ y ≤ chartAbsDens J A f φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSemiPosMassFinite».«chartDens_le_chartAbsDens» := P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_chartDens_le_chartAbsDens_dbc3b0b7f9dc
