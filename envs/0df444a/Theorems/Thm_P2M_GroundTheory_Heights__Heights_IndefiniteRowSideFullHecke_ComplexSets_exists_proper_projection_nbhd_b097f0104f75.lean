-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_proper_projection_nbhd_b097f0104f75
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_proper_projection_nbhd_b097f0104f75
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:43.09121+00:00
-- url     : https://prove2.me/theorems/357eabcf-e818-5dd3-b2da-c4d6db40f05e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists proper projection nbhd b097f0104f75: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists proper projection nbhd b097f0104f75 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists proper projection nbhd b097f0104f75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalParametrisation.lean#L11-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalParametrisation.lean#L11-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalParametrisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalParametrisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_proper_projection_nbhd_b097f0104f75 {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X w) (hw : w ∈ X)
    (hiso : ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) {U : Set (σ → ℂ)} (hU : U ∈ 𝓝 w) :
    ∃ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)), IsOpen B ∧ B ⊆ U ∧ w ∈ X ∩ B ∧ IsOpen D ∧
      IsPreconnected D ∧ Set.MapsTo A (X ∩ B) D ∧
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) ∧
      (∀ x ∈ X ∩ B, A x = A w → x = w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_proper_projection_nbhd» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_proper_projection_nbhd_b097f0104f75
