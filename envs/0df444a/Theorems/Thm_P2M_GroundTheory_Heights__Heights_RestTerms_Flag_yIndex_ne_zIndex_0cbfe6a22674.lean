-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_ne_zIndex_0cbfe6a22674
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_ne_zIndex_0cbfe6a22674
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:05.258649+00:00
-- url     : https://prove2.me/theorems/07dde4bd-a669-5b3b-a193-3d661fa54ed3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag y Index ne z Index 0cbfe6a22674: P2 M Ground Theory Heights  Heights Rest Terms Flag y Index ne z Index 0cbfe6a22674
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag y Index ne z Index 0cbfe6a22674 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag y Index ne z Index 0cbfe6a22674 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L170-L173

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
variable {f r a : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_ne_zIndex_0cbfe6a22674 (c : SmallBlock) (τ σ : Fin f) (l : Fin r) (i : Fin a) :
    yIndex f r a c τ l ≠ zIndex f r a c σ i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«yIndex_ne_zIndex» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_ne_zIndex_0cbfe6a22674
