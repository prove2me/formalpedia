-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_smul_mem_fibre_ea8dfa373a59
-- name    : P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_smul_mem_fibre_ea8dfa373a59
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:59.515949+00:00
-- url     : https://prove2.me/theorems/61c8faa5-6ddb-57ab-8050-b9363537722e
-- title:
--   P2 M Ground Theory Heights  Heights Pts Sheet Only Null smul mem fibre ea8dfa373a59: P2 M Ground Theory Heights  Heights Pts Sheet Only Null smul mem fibre ea8dfa373a59
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Sheet Only Null smul mem fibre ea8dfa373a59 construction uses the P2 M Ground Theory Heights  Heights Pts Sheet Only Null smul mem fibre ea8dfa373a59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L40-L46

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

theorem P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_smul_mem_fibre_ea8dfa373a59 {P : Ideal (MRing ι)} (hPh : IsMultiHomogIdeal P) [Nonempty K] {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) (Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (h0 : Ψ' (segre z) 0 ≠ 0) :
    (Ψ' (segre z) 0)⁻¹ • segre z ∈ fibre P Ψ' (ratio (Ψ' (segre z))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSheetOnlyNull».«smul_mem_fibre» := P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_smul_mem_fibre_ea8dfa373a59
