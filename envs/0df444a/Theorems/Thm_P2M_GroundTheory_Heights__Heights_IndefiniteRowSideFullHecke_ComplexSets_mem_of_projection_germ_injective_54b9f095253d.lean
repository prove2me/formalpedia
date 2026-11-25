-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_projection_germ_injective_54b9f095253d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_projection_germ_injective_54b9f095253d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:17.635196+00:00
-- url     : https://prove2.me/theorems/f61c3ce0-ebce-51d6-80dc-c30804ac8cb3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem of projection germ injective 54b9f095253d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comple
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem of projection germ injective 54b9f095253d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem of projection germ injective 54b9f095253d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteGermProjectionOpenAt.lean#L48-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteGermProjectionOpenAt.lean#L48-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteGermProjectionOpenAt
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_projection_germ_injective_54b9f095253d {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X x)
    (hinj : ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
      ∀ᶠ y in 𝓝 (A x), h y = 0) : x ∈ X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«mem_of_projection_germ_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_projection_germ_injective_54b9f095253d
