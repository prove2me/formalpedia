-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_zero_b1c44130856d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_zero_b1c44130856d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:56.822379+00:00
-- url     : https://prove2.me/theorems/17a9b488-df05-52ba-9d8c-231281071f82
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral zero b1c44130856d: P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral zero b1c44130856d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral zero b1c44130856d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral zero b1c44130856d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L225-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L225-L226

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
variable (f r a : ℕ) (c : SmallBlock)

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_zero_b1c44130856d (f N : ℕ) : flagIntegral f N 0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«flagIntegral_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_zero_b1c44130856d
