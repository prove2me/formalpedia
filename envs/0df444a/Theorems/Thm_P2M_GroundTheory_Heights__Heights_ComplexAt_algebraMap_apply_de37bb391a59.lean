-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59
-- name    : P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:21.6039+00:00
-- url     : https://prove2.me/theorems/83c13cc1-858f-4eff-bff3-ef1f7b8be125
-- title:
--   P2 M Ground Theory Heights  Heights Complex At algebra Map apply de37bb391a59: P2 M Ground Theory Heights  Heights Complex At algebra Map apply de37bb391a59
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex At algebra Map apply de37bb391a59 construction uses the P2 M Ground Theory Heights  Heights Complex At algebra Map apply de37bb391a59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L24-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexAt
variable {K : Type*} {_ : Field K} (σ : K →+* ℂ)

theorem P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59 (a : 𝓞 K) :
    algebraMap (𝓞 K) (ComplexAt σ) a = ofComplex σ (σ (a : K)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexAt».«algebraMap_apply» := P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59
