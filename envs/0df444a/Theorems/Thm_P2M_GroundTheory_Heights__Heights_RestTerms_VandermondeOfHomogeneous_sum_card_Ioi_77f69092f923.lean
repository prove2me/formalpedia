-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_VandermondeOfHomogeneous_sum_card_Ioi_77f69092f923
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_VandermondeOfHomogeneous_sum_card_Ioi_77f69092f923
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:35:59.445127+00:00
-- url     : https://prove2.me/theorems/795f845a-0f6e-4a28-807f-66b04c9a234f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Vandermonde Of Homogeneous sum card Ioi 77f69092f923: P2 M Ground Theory Heights  Heights Rest Terms Vandermonde Of Homogeneous sum card Ioi 77f69092f923
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Vandermonde Of Homogeneous sum card Ioi 77f69092f923 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Vandermonde Of Homogeneous sum card Ioi 77f69092f923 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PVandermondeOfHomogeneous.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PVandermondeOfHomogeneous.lean#L9-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_VandermondeOfHomogeneous_sum_card_Ioi_77f69092f923 (m : ℕ) :
    (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, (1 : ℕ)) = m * (m - 1) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«VandermondeOfHomogeneous».«sum_card_Ioi» := P2M_GroundTheory_Heights__Heights_RestTerms_VandermondeOfHomogeneous_sum_card_Ioi_77f69092f923
