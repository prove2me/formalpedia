-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreSpace_inner_equiv_9aa4479f01dc
-- name    : P2M_GroundTheory_Heights__Heights_FibreSpace_inner_equiv_9aa4479f01dc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:31.696965+00:00
-- url     : https://prove2.me/theorems/d026b739-183d-466a-9ba3-2766d75f695b
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Space inner equiv 9aa4479f01dc: P2 M Ground Theory Heights  Heights Fibre Space inner equiv 9aa4479f01dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Space inner equiv 9aa4479f01dc construction uses the P2 M Ground Theory Heights  Heights Fibre Space inner equiv 9aa4479f01dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianTensor.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianTensor.lean#L59-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianTensor
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
open GroundTheory.Heights₂.Heights.FibreSpace
variable (h : HermitianMetric K E) (σ : K →+* ℂ)

theorem P2M_GroundTheory_Heights__Heights_FibreSpace_inner_equiv_9aa4479f01dc (x y : Fibre σ E) :
    inner ℂ (equiv h σ x) (equiv h σ y) = (h.form σ).inner x y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreSpace».«inner_equiv» := P2M_GroundTheory_Heights__Heights_FibreSpace_inner_equiv_9aa4479f01dc
