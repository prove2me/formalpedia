-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_exp_branchLift_6efc6e3b6b62
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_exp_branchLift_6efc6e3b6b62
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:32.922527+00:00
-- url     : https://prove2.me/theorems/fd1206c3-6ffd-457e-b8fb-c1b849ce5a93
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent exp branch Lift 6efc6e3b6b62: P2 M Ground Theory Heights  Heights Regular Log Cover Descent exp branch Lift 6efc6e3b6b62
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent exp branch Lift 6efc6e3b6b62 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent exp branch Lift 6efc6e3b6b62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L116-L120

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

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_exp_branchLift_6efc6e3b6b62 {z0 z : Fin n → ℂ} {k : Fin n} (hk : k.val < a) (h0 : z0 k ≠ 0)
    (hz : z k ≠ 0) : Complex.exp (branchLift a z0 z k) = z k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«exp_branchLift» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_exp_branchLift_6efc6e3b6b62
