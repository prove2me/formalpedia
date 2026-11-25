-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_branchLift_mem_f862ff20aa70
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_branchLift_mem_f862ff20aa70
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:20.784478+00:00
-- url     : https://prove2.me/theorems/5e7eaafc-0a6f-5b1c-8f10-244979725adb
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent branch Lift mem f862ff20aa70: P2 M Ground Theory Heights  Heights Regular Log Cover Descent branch Lift mem f862ff20aa70
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent branch Lift mem f862ff20aa70 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent branch Lift mem f862ff20aa70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L122-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L122-L131

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

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_branchLift_mem_f862ff20aa70 {z0 z : Fin n → ℂ} (h0 : z0 ∈ puncturedChart h (ball 0 1))
    (hz : z ∈ puncturedChart h (ball 0 1)) : branchLift a z0 z ∈ logCover h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«branchLift_mem» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_branchLift_mem_f862ff20aa70
