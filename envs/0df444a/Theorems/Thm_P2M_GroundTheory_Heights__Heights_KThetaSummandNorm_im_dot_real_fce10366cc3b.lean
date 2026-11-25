-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_real_fce10366cc3b
-- name    : P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_real_fce10366cc3b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:17.202515+00:00
-- url     : https://prove2.me/theorems/bb736a67-4855-4591-9a35-a55cda0dbc84
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Summand Norm im dot real fce10366cc3b: P2 M Ground Theory Heights  Heights KTheta Summand Norm im dot real fce10366cc3b
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Summand Norm im dot real fce10366cc3b construction uses the P2 M Ground Theory Heights  Heights KTheta Summand Norm im dot real fce10366cc3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaSummandNorm.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaSummandNorm.lean#L20-L22

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

theorem P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_real_fce10366cc3b {g : ℕ} (w c : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ fun i => (c i : ℂ)).im = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaSummandNorm».«im_dot_real» := P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_im_dot_real_fce10366cc3b
