-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_span_fibreVec_cf563df73035
-- name    : P2M_GroundTheory_Heights__Heights_mem_span_fibreVec_cf563df73035
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:53.801354+00:00
-- url     : https://prove2.me/theorems/f528f471-332e-527e-82b3-2bc9f23c974b
-- title:
--   P2 M Ground Theory Heights  Heights mem span fibre Vec cf563df73035: P2 M Ground Theory Heights  Heights mem span fibre Vec cf563df73035
-- statement:
--   The P2 M Ground Theory Heights  Heights mem span fibre Vec cf563df73035 construction uses the P2 M Ground Theory Heights  Heights mem span fibre Vec cf563df73035 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L18-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L18-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (σ : K →+* ℂ)

theorem P2M_GroundTheory_Heights__Heights_mem_span_fibreVec_cf563df73035 {ι : Type*} [Fintype ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) (y : Fibre σ E) :
    FibreSpace.equiv h σ y ∈ Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_span_fibreVec» := P2M_GroundTheory_Heights__Heights_mem_span_fibreVec_cf563df73035
