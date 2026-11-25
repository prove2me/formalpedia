-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_zRoot_eq_blockEmb_92857d617718
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_zRoot_eq_blockEmb_92857d617718
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:09.288574+00:00
-- url     : https://prove2.me/theorems/def9726c-9b9b-4b50-9dc9-c29b9432130b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top z Root eq block Emb 92857d617718: P2 M Ground Theory Heights  Heights Rest Terms Top z Root eq block Emb 92857d617718
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top z Root eq block Emb 92857d617718 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top z Root eq block Emb 92857d617718 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L124-L126

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_zRoot_eq_blockEmb_92857d617718 (f r a : ℕ) (c : SmallBlock) (σ : Fin f) (i : Fin a) :
    zRoot f r a c σ i = blockEmb f (r + a) σ (zRoot 1 r a c 0 i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«zRoot_eq_blockEmb» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_zRoot_eq_blockEmb_92857d617718
