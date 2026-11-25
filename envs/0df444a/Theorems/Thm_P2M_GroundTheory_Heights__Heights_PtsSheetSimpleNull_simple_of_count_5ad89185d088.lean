-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_simple_of_count_5ad89185d088
-- name    : P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_simple_of_count_5ad89185d088
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:23:27.465547+00:00
-- url     : https://prove2.me/theorems/e765c88a-b37b-5aae-8e17-fa1777e06008
-- title:
--   P2 M Ground Theory Heights  Heights Pts Sheet Simple Null simple of count 5ad89185d088: P2 M Ground Theory Heights  Heights Pts Sheet Simple Null simple of count 5ad89185d088
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Sheet Simple Null simple of count 5ad89185d088 construction uses the P2 M Ground Theory Heights  Heights Pts Sheet Simple Null simple of count 5ad89185d088 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetSimpleNull.lean#L14-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetSimpleNull.lean#L14-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetSimpleNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsGenericCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetSimpleNull
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet segre_differentiableAt)

theorem P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_simple_of_count_5ad89185d088 {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {d : ℕ} {y : Fin e → ℂ}
    (hbd : ∀ y', (fibre P Ψ y').encard ≤ d) (hy : (fibre P Ψ y).encard = d)
    (hsh : ∀ w ∈ fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ) {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ fibre P Ψ y) : IsSimpleSheetPt P Ψ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSheetSimpleNull».«simple_of_count» := P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_simple_of_count_5ad89185d088
