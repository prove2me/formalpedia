-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_circle_smul_19f89149fa7e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_circle_smul_19f89149fa7e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:05.017339+00:00
-- url     : https://prove2.me/theorems/6a789770-08a7-485f-abfd-3b2a0e77a159
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel set Integral circle smul 19f89149fa7e: P2 M Ground Theory Heights  Heights Hilbert Samuel set Integral circle smul 19f89149fa7e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel set Integral circle smul 19f89149fa7e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel set Integral circle smul 19f89149fa7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L18-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PolydiscMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Metric Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_circle_smul_19f89149fa7e {D : ℕ} (u : Circle) (ρ : ℝ) (F : (Fin D → ℂ) → ℂ) :
    ∫ z in closedBall (0 : Fin D → ℂ) ρ, F ((u : ℂ) • z) =
      ∫ z in closedBall (0 : Fin D → ℂ) ρ, F z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«setIntegral_circle_smul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_circle_smul_19f89149fa7e
