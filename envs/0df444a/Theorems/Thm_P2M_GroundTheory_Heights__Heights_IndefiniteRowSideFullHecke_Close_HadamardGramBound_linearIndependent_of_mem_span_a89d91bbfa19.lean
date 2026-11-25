-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_HadamardGramBound_linearIndependent_of_mem_span_a89d91bbfa19
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_HadamardGramBound_linearIndependent_of_mem_span_a89d91bbfa19
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:44.567167+00:00
-- url     : https://prove2.me/theorems/c41b78a3-aef8-5977-85a9-cb9e89acc7ce
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Hadamard Gram Bound linear Independent of mem span a89d91bbfa19: P2 M Ground Theory Heights  Heights Indefinite Row Side Full H
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Hadamard Gram Bound linear Independent of mem span a89d91bbfa19 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Hadamard Gram Bound linear Independent of mem span a89d91bbfa19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LinearIndependentOfMemSpan.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LinearIndependentOfMemSpan.lean#L10-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LinearIndependentOfMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_HadamardGramBound_linearIndependent_of_mem_span_a89d91bbfa19 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℕ} (v b : Fin r → E) (hv : LinearIndependent ℝ v)
    (hb : ∀ i, v i ∈ Submodule.span ℤ (Set.range b)) : LinearIndependent ℝ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«HadamardGramBound».«linearIndependent_of_mem_span» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_HadamardGramBound_linearIndependent_of_mem_span_a89d91bbfa19
