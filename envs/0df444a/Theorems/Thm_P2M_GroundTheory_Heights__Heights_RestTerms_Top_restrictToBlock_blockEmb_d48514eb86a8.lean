-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrictToBlock_blockEmb_d48514eb86a8
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrictToBlock_blockEmb_d48514eb86a8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:35:48.836217+00:00
-- url     : https://prove2.me/theorems/1a085b30-4fd9-435f-ba17-c1b9507d5073
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top restrict To Block block Emb d48514eb86a8: P2 M Ground Theory Heights  Heights Rest Terms Top restrict To Block block Emb d48514eb86a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top restrict To Block block Emb d48514eb86a8 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top restrict To Block block Emb d48514eb86a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L36-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L36-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrictToBlock_blockEmb_d48514eb86a8 (f N : ℕ) (τ σ : Fin f) (P : RootRing 1 N) :
    restrictToBlock f N τ (blockEmb f N σ P) =
      if σ = τ then toN N P else C (constantCoeff P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«restrictToBlock_blockEmb» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrictToBlock_blockEmb_d48514eb86a8
