-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_sheetDensity_nonneg_55969338355e
-- name    : P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_sheetDensity_nonneg_55969338355e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T17:01:59.745733+00:00
-- url     : https://prove2.me/theorems/6d604f89-468e-50d5-bf7d-3965c50d2cc7
-- title:
--   P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite sheet Density nonneg 55969338355e: P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite sheet Density nonneg 55969338355e
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite sheet Density nonneg 55969338355e construction uses the P2 M Ground Theory Heights  Heights Pts Semi Pos Mass Finite sheet Density nonneg 55969338355e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSemiPosMassFinite.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSemiPosMassFinite.lean#L40-L51

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

theorem P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_sheetDensity_nonneg_55969338355e {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {N : Fin e → HermLine ι}
    (hNs : ∀ j, IsSmoothHerm (N j)) (hNp : ∀ j, Inter.IsSemiPosHerm (N j)) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : 0 ≤ sheetDensity P Ψ (pot N) (fun _ => 1) y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSemiPosMassFinite».«sheetDensity_nonneg» := P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_sheetDensity_nonneg_55969338355e
