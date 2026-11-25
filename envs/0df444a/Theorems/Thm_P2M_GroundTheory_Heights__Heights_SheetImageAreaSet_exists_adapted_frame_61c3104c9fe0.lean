-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_exists_adapted_frame_61c3104c9fe0
-- name    : P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_exists_adapted_frame_61c3104c9fe0
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:36.502381+00:00
-- url     : https://prove2.me/theorems/0b38c1c2-d1ae-4383-b723-117053766572
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Image Area Set exists adapted frame 61c3104c9fe0: P2 M Ground Theory Heights  Heights Sheet Image Area Set exists adapted frame 61c3104c9fe0
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Image Area Set exists adapted frame 61c3104c9fe0 construction uses the P2 M Ground Theory Heights  Heights Sheet Image Area Set exists adapted frame 61c3104c9fe0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageAreaSetFrame.lean#L14-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageAreaSetFrame.lean#L14-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
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
open Module
noncomputable section
open GroundTheory.Heights₂.Heights.SheetImageAreaSet

theorem P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_exists_adapted_frame_61c3104c9fe0 {n d : ℕ}
    (P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) (hP : Function.Surjective P) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m)
      (Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
      (L : EuclideanSpace ℂ (Fin d) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d))
      (π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)),
      (∀ z, ‖Q z‖ = ‖z‖) ∧
        ∀ z, Q z = WithLp.toLp 2 (fun j => Sum.elim (fun i => L (P z) i) (fun i => π z i) (e j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetImageAreaSet».«exists_adapted_frame» := P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_exists_adapted_frame_61c3104c9fe0
