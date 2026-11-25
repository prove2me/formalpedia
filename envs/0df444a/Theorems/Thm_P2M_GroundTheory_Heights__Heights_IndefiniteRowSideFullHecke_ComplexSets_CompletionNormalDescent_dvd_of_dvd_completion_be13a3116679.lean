-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_dvd_of_dvd_completion_be13a3116679
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_dvd_of_dvd_completion_be13a3116679
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:21.730454+00:00
-- url     : https://prove2.me/theorems/5c977caa-2d57-5e66-8b1f-913f902ef038
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Completion Normal Descent dvd of dvd completion be13a3116679: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Completion Normal Descent dvd of dvd completion be13a3116679 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Completion Normal Descent dvd of dvd completion be13a3116679 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCompletionNormalDescent.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCompletionNormalDescent.lean#L31-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompletionNormalDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCompletionNormalDescent
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
open AdicCompletion Polynomial
variable {R : Type} [CommRing R] (J : Ideal R)
variable [IsNoetherianRing R]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_dvd_of_dvd_completion_be13a3116679 (hJ : J ≤ (⊥ : Ideal R).jacobson) (a b : R)
    (x : AdicCompletion J R)
    (h : algebraMap R (AdicCompletion J R) a = algebraMap R (AdicCompletion J R) b * x) : b ∣ a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«CompletionNormalDescent».«dvd_of_dvd_completion» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_dvd_of_dvd_completion_be13a3116679
