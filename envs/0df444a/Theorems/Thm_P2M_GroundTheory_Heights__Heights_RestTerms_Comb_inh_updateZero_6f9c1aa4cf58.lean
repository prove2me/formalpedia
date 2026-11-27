-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_updateZero_6f9c1aa4cf58
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_updateZero_6f9c1aa4cf58
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:34:45.038338+00:00
-- url     : https://prove2.me/theorems/8d4bd23f-1a5e-522f-86bb-274c90cdc9cd
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb inh update Zero 6f9c1aa4cf58: P2 M Ground Theory Heights  Heights Rest Terms Comb inh update Zero 6f9c1aa4cf58
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb inh update Zero 6f9c1aa4cf58 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb inh update Zero 6f9c1aa4cf58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsComb.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsComb.lean#L31-L39

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_updateZero_6f9c1aa4cf58 :
    IsAlt (alternantPsum 2 [1]) ∧ Antitone (![1, 1] : Fin 2 → ℕ) ∧
      1 ≤ (![1, 1] : Fin 2 → ℕ) 0 + stair 2 0 ∧
      ¬ Antitone (Function.update (![1, 1] : Fin 2 → ℕ) 0 ((![1, 1] : Fin 2 → ℕ) 0 - 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«inh_updateZero» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_updateZero_6f9c1aa4cf58
