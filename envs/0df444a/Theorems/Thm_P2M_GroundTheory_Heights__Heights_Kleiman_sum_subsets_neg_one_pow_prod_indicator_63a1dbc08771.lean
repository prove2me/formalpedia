-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sum_subsets_neg_one_pow_prod_indicator_63a1dbc08771
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_sum_subsets_neg_one_pow_prod_indicator_63a1dbc08771
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:09.537779+00:00
-- url     : https://prove2.me/theorems/adc043fb-545a-4706-b1cb-dbcea7c9d7aa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman sum subsets neg one pow prod indicator 63a1dbc08771: P2 M Ground Theory Heights  Heights Kleiman sum subsets neg one pow prod indicator 63a1dbc08771
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman sum subsets neg one pow prod indicator 63a1dbc08771 construction uses the P2 M Ground Theory Heights  Heights Kleiman sum subsets neg one pow prod indicator 63a1dbc08771 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubsetDiffConst.lean#L11-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubsetDiffConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Kleiman_sum_subsets_neg_one_pow_prod_indicator_63a1dbc08771 (n : ℕ) (a : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, (if i ∈ T then (1 : ℚ) else 0) ^ a i =
      ∏ i, (1 - (0 : ℚ) ^ a i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«sum_subsets_neg_one_pow_prod_indicator» := P2M_GroundTheory_Heights__Heights_Kleiman_sum_subsets_neg_one_pow_prod_indicator_63a1dbc08771
