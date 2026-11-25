-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_logCover_nonempty_2f09675a86df
-- name    : P2M_GroundTheory_Heights__Heights_Regular_logCover_nonempty_2f09675a86df
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:04.292269+00:00
-- url     : https://prove2.me/theorems/1f23376a-1338-5e29-8c7b-7bc7135665db
-- title:
--   P2 M Ground Theory Heights  Heights Regular log Cover nonempty 2f09675a86df: P2 M Ground Theory Heights  Heights Regular log Cover nonempty 2f09675a86df
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular log Cover nonempty 2f09675a86df construction uses the P2 M Ground Theory Heights  Heights Regular log Cover nonempty 2f09675a86df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L113-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
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
open Metric Matrix Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_logCover_nonempty_2f09675a86df {n a : ℕ} (h : a ≤ n) : (logCover h).Nonempty := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«logCover_nonempty» := P2M_GroundTheory_Heights__Heights_Regular_logCover_nonempty_2f09675a86df
