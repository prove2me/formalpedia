-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_51072d07ff72
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_51072d07ff72
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:46.016325+00:00
-- url     : https://prove2.me/theorems/d8e46b58-a676-5949-b7f3-5c947e92fc7a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag block Sign mul 51072d07ff72: P2 M Ground Theory Heights  Heights Rest Terms Flag block Sign mul 51072d07ff72
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag block Sign mul 51072d07ff72 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag block Sign mul 51072d07ff72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L52-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_51072d07ff72 (f N : ℕ) (v w : Fin f → Equiv.Perm (Fin N)) :
    blockSign f N (v * w) = blockSign f N v * blockSign f N w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«blockSign_mul» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_51072d07ff72
