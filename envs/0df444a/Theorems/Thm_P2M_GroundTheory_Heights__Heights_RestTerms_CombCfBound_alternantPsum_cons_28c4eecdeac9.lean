-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_alternantPsum_cons_28c4eecdeac9
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_alternantPsum_cons_28c4eecdeac9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:05:25.746272+00:00
-- url     : https://prove2.me/theorems/c538ceb0-1b1f-4dfb-b7ea-252d5121b9ad
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound alternant Psum cons 28c4eecdeac9: P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound alternant Psum cons 28c4eecdeac9
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound alternant Psum cons 28c4eecdeac9 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Bound alternant Psum cons 28c4eecdeac9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfBound.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfBound.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Equiv Comb
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.CombCfBound

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_alternantPsum_cons_28c4eecdeac9 (m q : ℕ) (ρ : List ℕ) :
    alternantPsum m (q :: ρ) = alternantPsum m ρ * psum (Fin m) ℚ q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CombCfBound».«alternantPsum_cons» := P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_alternantPsum_cons_28c4eecdeac9
