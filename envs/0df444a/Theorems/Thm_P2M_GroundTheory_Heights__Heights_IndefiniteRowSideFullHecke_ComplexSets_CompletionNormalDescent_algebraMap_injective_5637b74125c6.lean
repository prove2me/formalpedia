-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_algebraMap_injective_5637b74125c6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_algebraMap_injective_5637b74125c6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:13.201398+00:00
-- url     : https://prove2.me/theorems/14ba39ec-25d2-4d72-9844-64fe0ac1985b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Completion Normal Descent algebra Map injective 5637b74125c6: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Completion Normal Descent algebra Map injective 5637b74125c6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Completion Normal Descent algebra Map injective 5637b74125c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCompletionNormalDescent.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCompletionNormalDescent.lean#L20-L29

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_algebraMap_injective_5637b74125c6 (hJ : J ≤ (⊥ : Ideal R).jacobson) :
    Function.Injective (algebraMap R (AdicCompletion J R)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«CompletionNormalDescent».«algebraMap_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_algebraMap_injective_5637b74125c6
