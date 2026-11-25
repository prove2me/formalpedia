-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_1e4d7c6c0226
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_1e4d7c6c0226
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:13.080346+00:00
-- url     : https://prove2.me/theorems/ceaa3e9d-2473-4fc1-a4bb-d0e1572557ae
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle quot norm eq 1e4d7c6c0226: P2 M Ground Theory Heights  Heights Hermitian Bundle quot norm eq 1e4d7c6c0226
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle quot norm eq 1e4d7c6c0226 construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle quot norm eq 1e4d7c6c0226 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsBundles.lean#L183-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsBundles.lean#L183-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianBundle
variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_1e4d7c6c0226 (σ : K →+* ℂ) (ξ : Fibre σ (M.carrier ⧸ F)) :
    ‖FibreSpace.equiv (M.quot F hF).metric σ ξ‖ = ‖quotFibreMap M F hF σ ξ‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«quot_norm_eq» := P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_1e4d7c6c0226
