-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaInnerMean_thetaSummand_shift_c27175728daa
-- name    : P2M_GroundTheory_Heights__Heights_KThetaInnerMean_thetaSummand_shift_c27175728daa
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:09.998284+00:00
-- url     : https://prove2.me/theorems/d04f1d64-ba57-4c58-bcba-c27646463ab9
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Inner Mean theta Summand shift c27175728daa: P2 M Ground Theory Heights  Heights KTheta Inner Mean theta Summand shift c27175728daa
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Inner Mean theta Summand shift c27175728daa construction uses the P2 M Ground Theory Heights  Heights KTheta Inner Mean theta Summand shift c27175728daa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaInnerMean.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaInnerMean.lean#L14-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaInnerMean
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
open Matrix Real MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaInnerMean

theorem P2M_GroundTheory_Heights__Heights_KThetaInnerMean_thetaSummand_shift_c27175728daa {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ)
    (k : Fin g → ℤ) :
    thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k =
      Complex.exp (((2 * π * ∑ i, a i * u₂ i : ℝ) : ℂ) * Complex.I) *
        (thetaSummand X Y a b
            (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k *
          torusChar k u₂) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaInnerMean».«thetaSummand_shift» := P2M_GroundTheory_Heights__Heights_KThetaInnerMean_thetaSummand_shift_c27175728daa
