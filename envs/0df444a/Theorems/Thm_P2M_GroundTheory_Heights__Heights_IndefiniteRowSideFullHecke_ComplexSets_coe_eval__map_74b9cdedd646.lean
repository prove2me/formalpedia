-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coe_eval__map_74b9cdedd646
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coe_eval__map_74b9cdedd646
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:14.376506+00:00
-- url     : https://prove2.me/theorems/5ce83404-ea69-5ae5-aa8b-253470501ae8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coe eval  map 74b9cdedd646: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coe eval  ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coe eval  map 74b9cdedd646 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coe eval  map 74b9cdedd646 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPrimitiveForm.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPrimitiveForm.lean#L167-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPrimitiveForm
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
open Topology Filter Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coe_eval__map_74b9cdedd646 {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (P : (analyticAtRing (A x))[X]) (v : analyticAtRing x) :
    ((eval₂ (alongPull X x A) (alongOf X x v) (P.map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
      ((eval₂ (preLinear x A) v.1 P : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«coe_eval₂_map» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coe_eval__map_74b9cdedd646
