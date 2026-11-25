-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RealSpace_norm_sq_eq_f71c520492db
-- name    : P2M_GroundTheory_Heights__Heights_RealSpace_norm_sq_eq_f71c520492db
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:34:26.480789+00:00
-- url     : https://prove2.me/theorems/d0a2cae3-a0c5-527e-a6b4-802b7a87c333
-- title:
--   P2 M Ground Theory Heights  Heights Real Space norm sq eq f71c520492db: P2 M Ground Theory Heights  Heights Real Space norm sq eq f71c520492db
-- statement:
--   The P2 M Ground Theory Heights  Heights Real Space norm sq eq f71c520492db construction uses the P2 M Ground Theory Heights  Heights Real Space norm sq eq f71c520492db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianEuclidean.lean#L168-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianEuclidean.lean#L168-L171

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K]
variable [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
variable (h : HermitianMetric K E)
open GroundTheory.Heights₂.Heights.RealSpace

theorem P2M_GroundTheory_Heights__Heights_RealSpace_norm_sq_eq_f71c520492db (x : RealSpace h) :
    ‖x‖ ^ 2 = ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
      (realToFibre σ E (equivTensor h x))).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RealSpace».«norm_sq_eq» := P2M_GroundTheory_Heights__Heights_RealSpace_norm_sq_eq_f71c520492db
