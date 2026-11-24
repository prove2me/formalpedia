-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreMap_tmul_6f6be11e0e36
-- name    : P2M_GroundTheory_Heights__Heights_fibreMap_tmul_6f6be11e0e36
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:17.611412+00:00
-- url     : https://prove2.me/theorems/664505a6-ec9f-4e7c-bf1f-4b04c0b1889b
-- title:
--   P2 M Ground Theory Heights  Heights fibre Map tmul 6f6be11e0e36: P2 M Ground Theory Heights  Heights fibre Map tmul 6f6be11e0e36
-- statement:
--   The P2 M Ground Theory Heights  Heights fibre Map tmul 6f6be11e0e36 construction uses the P2 M Ground Theory Heights  Heights fibre Map tmul 6f6be11e0e36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeIdeal.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeIdeal.lean#L40-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']
omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
  [Module.Finite (𝓞 K) E'] [Module.Projective (𝓞 K) E']

theorem P2M_GroundTheory_Heights__Heights_fibreMap_tmul_6f6be11e0e36 (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) (z : ComplexAt σ) (e : E') :
    fibreMap σ f (z ⊗ₜ e) = z ⊗ₜ f e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fibreMap_tmul» := P2M_GroundTheory_Heights__Heights_fibreMap_tmul_6f6be11e0e36
