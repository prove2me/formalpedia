-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaMean_continuous_exp_qf_add_4a3dae30bfe7
-- name    : P2M_GroundTheory_Heights__Heights_KThetaMean_continuous_exp_qf_add_4a3dae30bfe7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:59.871177+00:00
-- url     : https://prove2.me/theorems/2f1c4f72-5393-406b-94f5-2e2d3ca5a9ce
-- title:
--   P2 M Ground Theory Heights  Heights KTheta Mean continuous exp qf add 4a3dae30bfe7: P2 M Ground Theory Heights  Heights KTheta Mean continuous exp qf add 4a3dae30bfe7
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta Mean continuous exp qf add 4a3dae30bfe7 construction uses the P2 M Ground Theory Heights  Heights KTheta Mean continuous exp qf add 4a3dae30bfe7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaMean.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaMean.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaMean
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
open GroundTheory.Heights₂.Heights.KThetaMean
variable {g : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KThetaMean_continuous_exp_qf_add_4a3dae30bfe7 (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (a : Fin g → ℝ) :
    Continuous fun x : Fin g → ℝ => exp (-c * qf Y (x + a)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaMean».«continuous_exp_qf_add» := P2M_GroundTheory_Heights__Heights_KThetaMean_continuous_exp_qf_add_4a3dae30bfe7
