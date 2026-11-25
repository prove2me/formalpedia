-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sheetDensity_neg_9667c0f480de
-- name    : P2M_GroundTheory_Heights__Heights_sheetDensity_neg_9667c0f480de
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:15.959571+00:00
-- url     : https://prove2.me/theorems/ee44297a-d2de-5ce7-966c-7ee213cfa5b9
-- title:
--   P2 M Ground Theory Heights  Heights sheet Density neg 9667c0f480de: P2 M Ground Theory Heights  Heights sheet Density neg 9667c0f480de
-- statement:
--   The P2 M Ground Theory Heights  Heights sheet Density neg 9667c0f480de construction uses the P2 M Ground Theory Heights  Heights sheet Density neg 9667c0f480de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsIntegralProjIndep.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsIntegralProjIndep.lean#L22-L25

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
variable {K : Type*} [Fintype K] {ι : K → Type*} {e : ℕ} {P : Ideal (MRing ι)}
  {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ}

theorem P2M_GroundTheory_Heights__Heights_sheetDensity_neg_9667c0f480de (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sheetDensity_neg» := P2M_GroundTheory_Heights__Heights_sheetDensity_neg_9667c0f480de
