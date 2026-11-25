-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_exists_proj_ne_zero_40f19f1ce188
-- name    : P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_exists_proj_ne_zero_40f19f1ce188
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:57:20.440124+00:00
-- url     : https://prove2.me/theorems/4b02a66e-a0fc-427d-8bf6-61c74e567cb2
-- title:
--   P2 M Ground Theory Heights  Heights Pts Sheet Only Null exists proj ne zero 40f19f1ce188: P2 M Ground Theory Heights  Heights Pts Sheet Only Null exists proj ne zero 40f19f1ce188
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Sheet Only Null exists proj ne zero 40f19f1ce188 construction uses the P2 M Ground Theory Heights  Heights Pts Sheet Only Null exists proj ne zero 40f19f1ce188 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L122-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L122-L146

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

theorem P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_exists_proj_ne_zero_40f19f1ce188 (hC : CriticalFibreInfinite.Statement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P (e + 1)) {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsGoodProj P Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {V : Set (Fin e → ℂ)} (hV : IsOpen V)
    (hγ : ∀ y ∈ V, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    {y : Fin e → ℂ} (hy : y ∈ V) : ∃ y' ∈ V, Ψ' (segre (γ y')) 0 ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSheetOnlyNull».«exists_proj_ne_zero» := P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_exists_proj_ne_zero_40f19f1ce188
