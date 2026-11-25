-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_yEval_psum_c889ed04d6ec
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_yEval_psum_c889ed04d6ec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:20:47.928809+00:00
-- url     : https://prove2.me/theorems/f4d40e3e-706a-4e83-b16a-30e9554119d4
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top block Emb y Eval psum c889ed04d6ec: P2 M Ground Theory Heights  Heights Rest Terms Top block Emb y Eval psum c889ed04d6ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top block Emb y Eval psum c889ed04d6ec construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top block Emb y Eval psum c889ed04d6ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L147-L151

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_yEval_psum_c889ed04d6ec (f r a : ℕ) (c : SmallBlock) (σ : Fin f) (k : ℕ) :
    blockEmb f (r + a) σ (yEval r a c (psum (Fin r) ℚ k)) = smallPowerSum f r a c k σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«blockEmb_yEval_psum» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_yEval_psum_c889ed04d6ec
