-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaConstants_log_rhs_94d426c9282b
-- name    : P2M_GroundTheory_Heights__Heights_KThetaConstants_log_rhs_94d426c9282b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:25.256564+00:00
-- url     : https://prove2.me/theorems/e11b161b-a038-590e-bf9f-108b44b45341
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Constants log rhs 94d426c9282b: P2 M Ground Theory Heights  Heights KTheta Constants log rhs 94d426c9282b
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Constants log rhs 94d426c9282b construction uses the P2 M Ground Theory Heights  Heights KTheta Constants log rhs 94d426c9282b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaConstants.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaConstants.lean#L19-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaConstants
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
open Real
open GroundTheory.Heights₂.Heights.KThetaConstants

theorem P2M_GroundTheory_Heights__Heights_KThetaConstants_log_rhs_94d426c9282b (C ρ d : ℝ) (g : ℕ) (hd : 0 < d) :
    Real.log (((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) *
        exp (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g))) =
      (-(1 / 4)) * (g * Real.log 2 + Real.log d) +
        (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaConstants».«log_rhs» := P2M_GroundTheory_Heights__Heights_KThetaConstants_log_rhs_94d426c9282b
