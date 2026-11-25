-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RealSpace_inner_def_21a13e1f2e4d
-- name    : P2M_GroundTheory_Heights__Heights_RealSpace_inner_def_21a13e1f2e4d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:15:47.998859+00:00
-- url     : https://prove2.me/theorems/915c840a-c517-4135-9028-7c2bc5deb02a
-- title:
--   P2 M Ground Theory Heights  Heights Real Space inner def 21a13e1f2e4d: P2 M Ground Theory Heights  Heights Real Space inner def 21a13e1f2e4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Real Space inner def 21a13e1f2e4d construction uses the P2 M Ground Theory Heights  Heights Real Space inner def 21a13e1f2e4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianEuclidean.lean#L164-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianEuclidean.lean#L164-L166

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

theorem P2M_GroundTheory_Heights__Heights_RealSpace_inner_def_21a13e1f2e4d (x y : RealSpace h) :
    inner ℝ x y = ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
      (realToFibre σ E (equivTensor h y))).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RealSpace».«inner_def» := P2M_GroundTheory_Heights__Heights_RealSpace_inner_def_21a13e1f2e4d
