-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_sortShift_226779022f69
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_sortShift_226779022f69
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:35:19.579884+00:00
-- url     : https://prove2.me/theorems/cf0bbc79-18ea-4e4b-97fd-bd6961e9d471
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb inh sort Shift 226779022f69: P2 M Ground Theory Heights  Heights Rest Terms Comb inh sort Shift 226779022f69
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb inh sort Shift 226779022f69 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb inh sort Shift 226779022f69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsComb.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsComb.lean#L41-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsComb
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
open MvPolynomial Finset Equiv Comb
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_sortShift_226779022f69 :
    Antitone (![2, 1] : Fin 2 → ℕ) ∧ 1 ≤ (![2, 1] : Fin 2 → ℕ) 0 + stair 2 0 ∧
      Function.Injective (Function.update (fun j => (![2, 1] : Fin 2 → ℕ) j + stair 2 j) 0
        ((![2, 1] : Fin 2 → ℕ) 0 + stair 2 0 - 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«inh_sortShift» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_sortShift_226779022f69
