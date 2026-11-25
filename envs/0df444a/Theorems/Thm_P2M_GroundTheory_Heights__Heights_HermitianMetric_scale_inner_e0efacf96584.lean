-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianMetric_scale_inner_e0efacf96584
-- name    : P2M_GroundTheory_Heights__Heights_HermitianMetric_scale_inner_e0efacf96584
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:10.790071+00:00
-- url     : https://prove2.me/theorems/a02344aa-ef31-4574-96b6-cd5d511f7172
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Metric scale inner e0efacf96584: P2 M Ground Theory Heights  Heights Hermitian Metric scale inner e0efacf96584
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Metric scale inner e0efacf96584 construction uses the P2 M Ground Theory Heights  Heights Hermitian Metric scale inner e0efacf96584 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegree.lean#L397-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegree.lean#L397-L399

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

theorem P2M_GroundTheory_Heights__Heights_HermitianMetric_scale_inner_e0efacf96584 (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c)
    (σ : K →+* ℂ) (x y : Fibre σ E) :
    ((h.scale c hc).form σ).inner x y = ((c ^ 2 : ℝ) : ℂ) * (h.form σ).inner x y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianMetric».«scale_inner» := P2M_GroundTheory_Heights__Heights_HermitianMetric_scale_inner_e0efacf96584
