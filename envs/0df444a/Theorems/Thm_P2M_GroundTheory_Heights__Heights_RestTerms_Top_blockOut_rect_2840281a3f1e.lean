-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_rect_2840281a3f1e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_rect_2840281a3f1e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:20.92684+00:00
-- url     : https://prove2.me/theorems/aed1e6f6-c0c4-4049-bff5-ab859bc8fd28
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top block Out rect 2840281a3f1e: P2 M Ground Theory Heights  Heights Rest Terms Top block Out rect 2840281a3f1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top block Out rect 2840281a3f1e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top block Out rect 2840281a3f1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L177-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L177-L199

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_rect_2840281a3f1e (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) (h : q + m = r * a) :
    blockOut r a c κ q m = C (blockCoeff q m (rectangle r a) * κ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«blockOut_rect» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_rect_2840281a3f1e
