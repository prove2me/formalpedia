-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_ne_zero_of_mem_a8cb1672c599
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_ne_zero_of_mem_a8cb1672c599
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:24.551523+00:00
-- url     : https://prove2.me/theorems/0a0bd47c-2b38-403a-aba5-7bcae2b8e500
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent ne zero of mem a8cb1672c599: P2 M Ground Theory Heights  Heights Regular Log Cover Descent ne zero of mem a8cb1672c599
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent ne zero of mem a8cb1672c599 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent ne zero of mem a8cb1672c599 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L105-L109

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

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_ne_zero_of_mem_a8cb1672c599 {z : Fin n → ℂ} (hz : z ∈ puncturedChart h (ball 0 1)) (k : Fin n)
    (hk : k.val < a) : z k ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«ne_zero_of_mem» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_ne_zero_of_mem_a8cb1672c599
