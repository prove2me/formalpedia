-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_exp_mul_pow_le_44018617e26c
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_exp_mul_pow_le_44018617e26c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:44.143832+00:00
-- url     : https://prove2.me/theorems/bde0faa1-dacb-4143-b989-4bee14bde182
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail exp mul pow le 44018617e26c: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail exp mul pow le 44018617e26c
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail exp mul pow le 44018617e26c construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail exp mul pow le 44018617e26c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L70-L81

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

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_exp_mul_pow_le_44018617e26c {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : p ≤ 1) :
    Real.exp (-t) * t ^ p ≤ 2 * Real.exp (-(t / 2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«exp_mul_pow_le» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_exp_mul_pow_le_44018617e26c
