-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_eval_27b94d595884
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_eval_27b94d595884
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:13.92253+00:00
-- url     : https://prove2.me/theorems/0e98979c-22fc-4fee-9b20-d00ddaf8fdd8
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent analytic At eval 27b94d595884: P2 M Ground Theory Heights  Heights Regular Log Cover Descent analytic At eval 27b94d595884
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent analytic At eval 27b94d595884 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent analytic At eval 27b94d595884 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L102-L103

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

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_eval_27b94d595884 (k : Fin n) (z : Fin n → ℂ) : AnalyticAt ℂ (fun z : Fin n → ℂ => z k) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«analyticAt_eval» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_eval_27b94d595884
