-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_sum_fin_staircase_2e9ed8b6be52
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_sum_fin_staircase_2e9ed8b6be52
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:20:17.76268+00:00
-- url     : https://prove2.me/theorems/c352af17-7e75-4d01-b8f2-fb9ae473ae05
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product sum fin staircase 2e9ed8b6be52: P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product sum fin staircase 2e9ed8b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product sum fin staircase 2e9ed8b6be52 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product sum fin staircase 2e9ed8b6be52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSmallBlockProduct.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSmallBlockProduct.lean#L14-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSmallBlockProduct
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
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_sum_fin_staircase_2e9ed8b6be52 (r : ℕ) : ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchSmallBlockProduct».«sum_fin_staircase» := P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_sum_fin_staircase_2e9ed8b6be52
