-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_integral_Icc_exp_b28c0fec4769
-- name    : P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_integral_Icc_exp_b28c0fec4769
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:21.243242+00:00
-- url     : https://prove2.me/theorems/da711c16-ec37-5e9c-927f-599858ba58d2
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Char Integral integral Icc exp b28c0fec4769: P2 M Ground Theory Heights  Heights KTheta Char Integral integral Icc exp b28c0fec4769
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Char Integral integral Icc exp b28c0fec4769 construction uses the P2 M Ground Theory Heights  Heights KTheta Char Integral integral Icc exp b28c0fec4769 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaCharIntegral.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaCharIntegral.lean#L13-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCharIntegral
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
open Real MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaCharIntegral

theorem P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_integral_Icc_exp_b28c0fec4769 (n : ℤ) :
    ∫ t in Set.Icc (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((n : ℂ) * (t : ℂ))) =
      if n = 0 then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaCharIntegral».«integral_Icc_exp» := P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_integral_Icc_exp_b28c0fec4769
