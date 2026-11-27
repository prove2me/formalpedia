-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_conjMap_smul_962c21f8b3dc
-- name    : P2M_GroundTheory_Heights__Heights_conjMap_smul_962c21f8b3dc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:44.765513+00:00
-- url     : https://prove2.me/theorems/221ecde7-d18f-4c71-b467-77699f9f5811
-- title:
--   P2 M Ground Theory Heights  Heights conj Map smul 962c21f8b3dc: P2 M Ground Theory Heights  Heights conj Map smul 962c21f8b3dc
-- statement:
--   The P2 M Ground Theory Heights  Heights conj Map smul 962c21f8b3dc construction uses the P2 M Ground Theory Heights  Heights conj Map smul 962c21f8b3dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianLattice.lean#L76-L81

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
open ComplexAt
variable {K : Type*} [Field K]
variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]
variable {σ E}

theorem P2M_GroundTheory_Heights__Heights_conjMap_smul_962c21f8b3dc (c : ℂ) (x : Fibre σ E) :
    conjMap σ E (c • x) = starRingEnd ℂ c • conjMap σ E x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«conjMap_smul» := P2M_GroundTheory_Heights__Heights_conjMap_smul_962c21f8b3dc
