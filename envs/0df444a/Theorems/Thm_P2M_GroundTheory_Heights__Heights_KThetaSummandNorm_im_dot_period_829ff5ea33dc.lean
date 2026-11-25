-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_period_829ff5ea33dc
-- name    : P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_period_829ff5ea33dc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:25:54.883447+00:00
-- url     : https://prove2.me/theorems/3c09e1a6-d9d9-47ff-a680-36f7340dca5f
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Summand Norm im dot period 829ff5ea33dc: P2 M Ground Theory Heights  Heights KTheta Summand Norm im dot period 829ff5ea33dc
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Summand Norm im dot period 829ff5ea33dc construction uses the P2 M Ground Theory Heights  Heights KTheta Summand Norm im dot period 829ff5ea33dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaSummandNorm.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaSummandNorm.lean#L13-L18

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

theorem P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_period_829ff5ea33dc {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (w v : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (v i : ℂ))).im = w ⬝ᵥ (Y *ᵥ v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaSummandNorm».«im_dot_period» := P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_period_829ff5ea33dc
