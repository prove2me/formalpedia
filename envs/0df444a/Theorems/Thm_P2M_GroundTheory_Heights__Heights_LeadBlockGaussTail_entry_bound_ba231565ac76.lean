-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_entry_bound_ba231565ac76
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_entry_bound_ba231565ac76
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:04.173816+00:00
-- url     : https://prove2.me/theorems/7bf99ee1-4a39-42a2-80fe-0d5f429f8b03
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail entry bound ba231565ac76: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail entry bound ba231565ac76
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail entry bound ba231565ac76 construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail entry bound ba231565ac76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L83-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L83-L155

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_entry_bound_ba231565ac76 (ρ : ℝ) (p : ℕ) (hp : p ≤ 1) :
    ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ p) * ballInd ρ z ≤
      ENNReal.ofReal (entryConst / (1 + ρ ^ 2) ^ (p + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«entry_bound» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_entry_bound_ba231565ac76
