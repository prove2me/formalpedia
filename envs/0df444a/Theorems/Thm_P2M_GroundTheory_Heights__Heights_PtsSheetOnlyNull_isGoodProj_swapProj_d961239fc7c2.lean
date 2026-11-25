-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_isGoodProj_swapProj_d961239fc7c2
-- name    : P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_isGoodProj_swapProj_d961239fc7c2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:53.276949+00:00
-- url     : https://prove2.me/theorems/46e3c9f9-10d3-5192-bc02-c0f17cc22a41
-- title:
--   P2 M Ground Theory Heights  Heights Pts Sheet Only Null is Good Proj swap Proj d961239fc7c2: P2 M Ground Theory Heights  Heights Pts Sheet Only Null is Good Proj swap Proj d961239fc7c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Sheet Only Null is Good Proj swap Proj d961239fc7c2 construction uses the P2 M Ground Theory Heights  Heights Pts Sheet Only Null is Good Proj swap Proj d961239fc7c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L69-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt

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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj IsMultiHomogIdeal mcPts segre fibre IsSheet scaleBlock
  scaleBlock_mem_zeroLocus segre_differentiableAt osgood fibreFinite)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_isGoodProj_swapProj_d961239fc7c2 {P : Ideal (MRing ι)} {Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hΨ' : IsGoodProj P Ψ') (j : Fin (e + 1)) : IsGoodProj P (swapProj j Ψ') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSheetOnlyNull».«isGoodProj_swapProj» := P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_isGoodProj_swapProj_d961239fc7c2
