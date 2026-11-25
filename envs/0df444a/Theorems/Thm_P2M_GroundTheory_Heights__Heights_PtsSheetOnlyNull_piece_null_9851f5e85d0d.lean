-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_piece_null_9851f5e85d0d
-- name    : P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_piece_null_9851f5e85d0d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:57:26.554428+00:00
-- url     : https://prove2.me/theorems/b63ccffc-646f-4410-8cc7-2c81c18ec059
-- title:
--   P2 M Ground Theory Heights  Heights Pts Sheet Only Null piece null 9851f5e85d0d: P2 M Ground Theory Heights  Heights Pts Sheet Only Null piece null 9851f5e85d0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Sheet Only Null piece null 9851f5e85d0d construction uses the P2 M Ground Theory Heights  Heights Pts Sheet Only Null piece null 9851f5e85d0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L255-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L255-L315

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

theorem P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_piece_null_9851f5e85d0d (hC : CriticalFibreInfinite.Statement) {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsGoodProj P Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {O : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hOo : IsOpen O)
    (hO : ∀ q ∈ O, (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ mcPts P ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
      (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1))) :
    volume {y | (y, segre (γ y)) ∈ O ∧
      ¬ IsSimpleSheetPt P Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))} = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSheetOnlyNull».«piece_null» := P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_piece_null_9851f5e85d0d
