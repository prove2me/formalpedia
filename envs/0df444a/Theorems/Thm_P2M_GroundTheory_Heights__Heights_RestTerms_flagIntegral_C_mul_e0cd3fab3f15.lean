-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_C_mul_e0cd3fab3f15
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_C_mul_e0cd3fab3f15
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:35:53.237124+00:00
-- url     : https://prove2.me/theorems/5d09c414-b407-473b-9297-7aafba718e2d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms flag Integral C mul e0cd3fab3f15: P2 M Ground Theory Heights  Heights Rest Terms flag Integral C mul e0cd3fab3f15
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms flag Integral C mul e0cd3fab3f15 construction uses the P2 M Ground Theory Heights  Heights Rest Terms flag Integral C mul e0cd3fab3f15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L29-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_C_mul_e0cd3fab3f15 (f N : ℕ) (b : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C b * Φ) = b * flagIntegral f N Φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«flagIntegral_C_mul» := P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_C_mul_e0cd3fab3f15
