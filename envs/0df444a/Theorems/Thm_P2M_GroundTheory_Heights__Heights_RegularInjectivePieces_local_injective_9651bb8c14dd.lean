-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegularInjectivePieces_local_injective_9651bb8c14dd
-- name    : P2M_GroundTheory_Heights__Heights_RegularInjectivePieces_local_injective_9651bb8c14dd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:44.829424+00:00
-- url     : https://prove2.me/theorems/afac5f31-140a-5249-b716-342a9eeb590c
-- title:
--   P2 M Ground Theory Heights  Heights Regular Injective Pieces local injective 9651bb8c14dd: P2 M Ground Theory Heights  Heights Regular Injective Pieces local injective 9651bb8c14dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Injective Pieces local injective 9651bb8c14dd construction uses the P2 M Ground Theory Heights  Heights Regular Injective Pieces local injective 9651bb8c14dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularInjectivePieces.lean#L24-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularInjectivePieces.lean#L24-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularInjectivePieces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularInjectivePieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.RegularInjectivePieces

theorem P2M_GroundTheory_Heights__Heights_RegularInjectivePieces_local_injective_9651bb8c14dd {d : ℕ} {U : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → Fin d → ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) :
    IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧
    ∀ w ∈ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0},
      ∃ V : Set (Fin d → ℂ), IsOpen V ∧ w ∈ V ∧
        V ⊆ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧ Set.InjOn g V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegularInjectivePieces».«local_injective» := P2M_GroundTheory_Heights__Heights_RegularInjectivePieces_local_injective_9651bb8c14dd
