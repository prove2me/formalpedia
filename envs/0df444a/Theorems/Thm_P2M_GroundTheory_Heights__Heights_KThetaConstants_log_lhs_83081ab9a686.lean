-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaConstants_log_lhs_83081ab9a686
-- name    : P2M_GroundTheory_Heights__Heights_KThetaConstants_log_lhs_83081ab9a686
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:42.454798+00:00
-- url     : https://prove2.me/theorems/c0ed46b1-b4d3-4dec-8fac-b22b08224920
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Constants log lhs 83081ab9a686: P2 M Ground Theory Heights  Heights KTheta Constants log lhs 83081ab9a686
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Constants log lhs 83081ab9a686 construction uses the P2 M Ground Theory Heights  Heights KTheta Constants log lhs 83081ab9a686 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaConstants.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaConstants.lean#L11-L17

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

theorem P2M_GroundTheory_Heights__Heights_KThetaConstants_log_lhs_83081ab9a686 (C₃ ρ d : ℝ) (g : ℕ) (hC₃ : 0 < C₃) (hg : (0 : ℝ) < g) (hρ : 0 < ρ) (hd : 0 < d) :
    Real.log ((C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g) =
      (g / 2) * Real.log (C₃ * g) + (-(1 / 2)) * Real.log d + g * Real.log (1 + 1 / ρ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaConstants».«log_lhs» := P2M_GroundTheory_Heights__Heights_KThetaConstants_log_lhs_83081ab9a686
