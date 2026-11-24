-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_lTensor_complex_smul_450d1267bf4b
-- name    : P2M_GroundTheory_Heights__Heights_lTensor_complex_smul_450d1267bf4b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:47.595094+00:00
-- url     : https://prove2.me/theorems/fa5c4f32-1214-4148-aca0-4e5c9ca952c3
-- title:
--   P2 M Ground Theory Heights  Heights l Tensor complex smul 450d1267bf4b: P2 M Ground Theory Heights  Heights l Tensor complex smul 450d1267bf4b
-- statement:
--   The P2 M Ground Theory Heights  Heights l Tensor complex smul 450d1267bf4b construction uses the P2 M Ground Theory Heights  Heights l Tensor complex smul 450d1267bf4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L56-L62

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
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_lTensor_complex_smul_450d1267bf4b (σ : K →+* ℂ) {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] (f : M →ₗ[𝓞 K] N) (c : ℂ) (x : Fibre σ M) :
    f.lTensor (ComplexAt σ) (c • x) = c • f.lTensor (ComplexAt σ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«lTensor_complex_smul» := P2M_GroundTheory_Heights__Heights_lTensor_complex_smul_450d1267bf4b
