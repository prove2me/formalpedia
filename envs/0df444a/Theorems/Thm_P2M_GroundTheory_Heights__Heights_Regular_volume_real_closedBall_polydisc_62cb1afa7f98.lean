-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_volume_real_closedBall_polydisc_62cb1afa7f98
-- name    : P2M_GroundTheory_Heights__Heights_Regular_volume_real_closedBall_polydisc_62cb1afa7f98
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:47.114632+00:00
-- url     : https://prove2.me/theorems/96228b6f-f577-54cc-8534-97ce32d45413
-- title:
--   P2 M Ground Theory Heights  Heights Regular volume real closed Ball polydisc 62cb1afa7f98: P2 M Ground Theory Heights  Heights Regular volume real closed Ball polydisc 62cb1afa7f98
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular volume real closed Ball polydisc 62cb1afa7f98 construction uses the P2 M Ground Theory Heights  Heights Regular volume real closed Ball polydisc 62cb1afa7f98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifierLowerBound.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifierLowerBound.lean#L13-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifierLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Set
open ReciprocityTheory.AnForm.A
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_volume_real_closedBall_polydisc_62cb1afa7f98 {D : ℕ} (x : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = (Real.pi * r ^ 2) ^ D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«volume_real_closedBall_polydisc» := P2M_GroundTheory_Heights__Heights_Regular_volume_real_closedBall_polydisc_62cb1afa7f98
