-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_add_mem_logCover_iff_993127721c12
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_add_mem_logCover_iff_993127721c12
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:26.42806+00:00
-- url     : https://prove2.me/theorems/10fbed8f-c5c3-4e3d-aa76-513fa7ad7a9a
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent add mem log Cover iff 993127721c12: P2 M Ground Theory Heights  Heights Regular Log Cover Descent add mem log Cover iff 993127721c12
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent add mem log Cover iff 993127721c12 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent add mem log Cover iff 993127721c12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L15-L25

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

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_add_mem_logCover_iff_993127721c12 {v : Fin n → ℂ} (hre : ∀ k : Fin n, (v k).re = 0)
    (hz : ∀ k : Fin n, a ≤ k.val → v k = 0) (w : Fin n → ℂ) :
    w + v ∈ logCover h ↔ w ∈ logCover h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«add_mem_logCover_iff» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_add_mem_logCover_iff_993127721c12
