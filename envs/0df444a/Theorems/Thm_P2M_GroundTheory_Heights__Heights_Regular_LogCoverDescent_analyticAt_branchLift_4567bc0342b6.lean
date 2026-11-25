-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_branchLift_4567bc0342b6
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_branchLift_4567bc0342b6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:06.146483+00:00
-- url     : https://prove2.me/theorems/8b5a0282-c3aa-40ed-9f4a-772f80678724
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent analytic At branch Lift 4567bc0342b6: P2 M Ground Theory Heights  Heights Regular Log Cover Descent analytic At branch Lift 4567bc0342b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent analytic At branch Lift 4567bc0342b6 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent analytic At branch Lift 4567bc0342b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L134-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L134-L144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent
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
open Metric Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
variable {n a : ℕ} (h : a ≤ n)
variable {h}
omit h

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_branchLift_4567bc0342b6 {z0 : Fin n → ℂ} (h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0) :
    AnalyticAt ℂ (branchLift a z0) z0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«analyticAt_branchLift» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_branchLift_4567bc0342b6
