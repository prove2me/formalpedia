-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_degree_line_indep_855d717e1a04
-- name    : P2M_GroundTheory_Heights__Heights_degree_line_indep_855d717e1a04
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:08.666566+00:00
-- url     : https://prove2.me/theorems/ea3e3b0b-168c-4c89-add7-71005b3add97
-- title:
--   P2 M Ground Theory Heights  Heights degree line indep 855d717e1a04: P2 M Ground Theory Heights  Heights degree line indep 855d717e1a04
-- statement:
--   The P2 M Ground Theory Heights  Heights degree line indep 855d717e1a04 construction uses the P2 M Ground Theory Heights  Heights degree line indep 855d717e1a04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegree.lean#L340-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegree.lean#L340-L345

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
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
  [Module.Projective (𝓞 K) E]

theorem P2M_GroundTheory_Heights__Heights_degree_line_indep_855d717e1a04 (h : HermitianMetric K E) (hE : Module.finrank (𝓞 K) E = 1) {s t : E}
    (hs : s ≠ 0) (ht : t ≠ 0) :
    Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) {s})) - ∑ σ : K →+* ℂ, Real.log ‖fibreVec h σ s‖ =
      Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) {t})) -
        ∑ σ : K →+* ℂ, Real.log ‖fibreVec h σ t‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«degree_line_indep» := P2M_GroundTheory_Heights__Heights_degree_line_indep_855d717e1a04
