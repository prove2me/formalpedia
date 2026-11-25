-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_qf_add_272ec1b90821
-- name    : P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_qf_add_272ec1b90821
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:15.465929+00:00
-- url     : https://prove2.me/theorems/617d5fc8-9e85-4a6a-a1fc-14719b40b0a4
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Summand Norm qf add 272ec1b90821: P2 M Ground Theory Heights  Heights KTheta Summand Norm qf add 272ec1b90821
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Summand Norm qf add 272ec1b90821 construction uses the P2 M Ground Theory Heights  Heights KTheta Summand Norm qf add 272ec1b90821 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaSummandNorm.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaSummandNorm.lean#L24-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaSummandNorm
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
open Matrix Real
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaSummandNorm

theorem P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_qf_add_272ec1b90821 {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.IsSymm) (w u : Fin g → ℝ) :
    qf Y (w + u) = qf Y w + 2 * (w ⬝ᵥ (Y *ᵥ u)) + qf Y u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaSummandNorm».«qf_add» := P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_qf_add_272ec1b90821
