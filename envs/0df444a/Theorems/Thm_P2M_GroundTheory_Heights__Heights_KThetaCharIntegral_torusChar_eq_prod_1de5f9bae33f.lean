-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_torusChar_eq_prod_1de5f9bae33f
-- name    : P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_torusChar_eq_prod_1de5f9bae33f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:16.976184+00:00
-- url     : https://prove2.me/theorems/cbe9f09a-da33-5948-9e82-4acf237305e1
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Char Integral torus Char eq prod 1de5f9bae33f: P2 M Ground Theory Heights  Heights KTheta Char Integral torus Char eq prod 1de5f9bae33f
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Char Integral torus Char eq prod 1de5f9bae33f construction uses the P2 M Ground Theory Heights  Heights KTheta Char Integral torus Char eq prod 1de5f9bae33f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaCharIntegral.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaCharIntegral.lean#L31-L34

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

theorem P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_torusChar_eq_prod_1de5f9bae33f {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = ∏ i, Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (u i : ℂ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaCharIntegral».«torusChar_eq_prod» := P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_torusChar_eq_prod_1de5f9bae33f
