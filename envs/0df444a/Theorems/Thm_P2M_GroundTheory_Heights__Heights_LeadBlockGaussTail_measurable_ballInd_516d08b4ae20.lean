-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_measurable_ballInd_516d08b4ae20
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_measurable_ballInd_516d08b4ae20
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:22.724795+00:00
-- url     : https://prove2.me/theorems/e2004fbc-375e-42cf-b169-2e46e13c69d8
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail measurable ball Ind 516d08b4ae20: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail measurable ball Ind 516d08b4ae20
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail measurable ball Ind 516d08b4ae20 construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail measurable ball Ind 516d08b4ae20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L60-L61

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

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_measurable_ballInd_516d08b4ae20 (ρ : ℝ) : Measurable (ballInd ρ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«measurable_ballInd» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_measurable_ballInd_516d08b4ae20
