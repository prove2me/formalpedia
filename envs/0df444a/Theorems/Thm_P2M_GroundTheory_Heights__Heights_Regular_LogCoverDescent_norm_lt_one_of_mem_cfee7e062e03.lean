-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_norm_lt_one_of_mem_cfee7e062e03
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_norm_lt_one_of_mem_cfee7e062e03
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:18.28895+00:00
-- url     : https://prove2.me/theorems/307f1181-9122-46d5-9a86-e8fedb4d9e5f
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent norm lt one of mem cfee7e062e03: P2 M Ground Theory Heights  Heights Regular Log Cover Descent norm lt one of mem cfee7e062e03
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent norm lt one of mem cfee7e062e03 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent norm lt one of mem cfee7e062e03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L111-L113

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

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_norm_lt_one_of_mem_cfee7e062e03 {z : Fin n → ℂ} (hz : z ∈ puncturedChart h (ball 0 1)) (k : Fin n) :
    ‖z k‖ < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«norm_lt_one_of_mem» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_norm_lt_one_of_mem_cfee7e062e03
