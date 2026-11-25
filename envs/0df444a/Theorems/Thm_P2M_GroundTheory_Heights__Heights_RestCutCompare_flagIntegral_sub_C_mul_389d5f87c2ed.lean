-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutCompare_flagIntegral_sub_C_mul_389d5f87c2ed
-- name    : P2M_GroundTheory_Heights__Heights_RestCutCompare_flagIntegral_sub_C_mul_389d5f87c2ed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:57.158626+00:00
-- url     : https://prove2.me/theorems/54b628f6-8650-57f5-8384-487826da68f5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Compare flag Integral sub C mul 389d5f87c2ed: P2 M Ground Theory Heights  Heights Rest Cut Compare flag Integral sub C mul 389d5f87c2ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Compare flag Integral sub C mul 389d5f87c2ed construction uses the P2 M Ground Theory Heights  Heights Rest Cut Compare flag Integral sub C mul 389d5f87c2ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCompare.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCompare.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCompare
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_RestCutCompare_flagIntegral_sub_C_mul_389d5f87c2ed (f N : ℕ) (P Q : RestTerms.RootRing f N) (b : ℚ) :
    RestTerms.flagIntegral f N (P - C b * Q) =
      RestTerms.flagIntegral f N P - b * RestTerms.flagIntegral f N Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutCompare».«flagIntegral_sub_C_mul» := P2M_GroundTheory_Heights__Heights_RestCutCompare_flagIntegral_sub_C_mul_389d5f87c2ed
