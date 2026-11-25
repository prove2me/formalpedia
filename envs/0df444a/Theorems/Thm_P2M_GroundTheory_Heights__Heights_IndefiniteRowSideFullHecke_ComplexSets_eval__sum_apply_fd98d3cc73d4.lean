-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval__sum_apply_fd98d3cc73d4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval__sum_apply_fd98d3cc73d4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:47.292354+00:00
-- url     : https://prove2.me/theorems/7ebedbb4-e158-50b5-875e-94b240da1105
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval  sum apply fd98d3cc73d4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval  sum
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval  sum apply fd98d3cc73d4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval  sum apply fd98d3cc73d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPrimitiveForm.lean#L184-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPrimitiveForm.lean#L184-L187

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval__sum_apply_fd98d3cc73d4 {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (g : (σ → ℂ) → ℂ) {M : ℕ} (b : Fin M → analyticAtRing (A x)) (z : σ → ℂ) :
    eval₂ (preLinear x A) g (∑ j, C (b j) * X ^ (j : ℕ)) z = ∑ j, (b j).1 (A z) * g z ^ (j : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eval₂_sum_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval__sum_apply_fd98d3cc73d4
