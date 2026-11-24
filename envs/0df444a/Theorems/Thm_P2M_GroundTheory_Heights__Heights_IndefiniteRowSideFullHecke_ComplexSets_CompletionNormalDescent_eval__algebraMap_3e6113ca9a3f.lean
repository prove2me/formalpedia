-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_eval__algebraMap_3e6113ca9a3f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_eval__algebraMap_3e6113ca9a3f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:57.569869+00:00
-- url     : https://prove2.me/theorems/767aeadf-868c-414b-aba8-900274493dfe
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Completion Normal Descent eval  algebra Map 3e6113ca9a3f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full H
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Completion Normal Descent eval  algebra Map 3e6113ca9a3f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Completion Normal Descent eval  algebra Map 3e6113ca9a3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCompletionNormalDescent.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCompletionNormalDescent.lean#L13-L16

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_eval__algebraMap_3e6113ca9a3f (n : ℕ) (x : R) :
    evalₐ J n (algebraMap R (AdicCompletion J R) x) = Ideal.Quotient.mk (J ^ n) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«CompletionNormalDescent».«evalₐ_algebraMap» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_eval__algebraMap_3e6113ca9a3f
