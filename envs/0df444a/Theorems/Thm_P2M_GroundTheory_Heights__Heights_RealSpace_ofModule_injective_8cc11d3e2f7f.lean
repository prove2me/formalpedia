-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RealSpace_ofModule_injective_8cc11d3e2f7f
-- name    : P2M_GroundTheory_Heights__Heights_RealSpace_ofModule_injective_8cc11d3e2f7f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:15:37.862567+00:00
-- url     : https://prove2.me/theorems/b611a5ed-2e58-4cbd-8574-6f0f511c21b2
-- title:
--   P2 M Ground Theory Heights  Heights Real Space of Module injective 8cc11d3e2f7f: P2 M Ground Theory Heights  Heights Real Space of Module injective 8cc11d3e2f7f
-- statement:
--   The P2 M Ground Theory Heights  Heights Real Space of Module injective 8cc11d3e2f7f construction uses the P2 M Ground Theory Heights  Heights Real Space of Module injective 8cc11d3e2f7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianEuclidean.lean#L206-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianEuclidean.lean#L206-L215

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

theorem P2M_GroundTheory_Heights__Heights_RealSpace_ofModule_injective_8cc11d3e2f7f : Function.Injective (ofModule h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RealSpace».«ofModule_injective» := P2M_GroundTheory_Heights__Heights_RealSpace_ofModule_injective_8cc11d3e2f7f
