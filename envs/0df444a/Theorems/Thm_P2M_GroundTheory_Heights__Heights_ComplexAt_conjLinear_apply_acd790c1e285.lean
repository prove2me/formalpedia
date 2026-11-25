-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_conjLinear_apply_acd790c1e285
-- name    : P2M_GroundTheory_Heights__Heights_ComplexAt_conjLinear_apply_acd790c1e285
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:08:59.400403+00:00
-- url     : https://prove2.me/theorems/6d380b38-a00b-5000-8f7e-7ff3ad3c9ad1
-- title:
--   P2 M Ground Theory Heights  Heights Complex At conj Linear apply acd790c1e285: P2 M Ground Theory Heights  Heights Complex At conj Linear apply acd790c1e285
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex At conj Linear apply acd790c1e285 construction uses the P2 M Ground Theory Heights  Heights Complex At conj Linear apply acd790c1e285 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L50-L50

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

theorem P2M_GroundTheory_Heights__Heights_ComplexAt_conjLinear_apply_acd790c1e285 (z : ComplexAt σ) : conjLinear σ z = conj σ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexAt».«conjLinear_apply» := P2M_GroundTheory_Heights__Heights_ComplexAt_conjLinear_apply_acd790c1e285
