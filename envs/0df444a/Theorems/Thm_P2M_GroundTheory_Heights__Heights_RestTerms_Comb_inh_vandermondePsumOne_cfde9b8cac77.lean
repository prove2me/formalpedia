-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_vandermondePsumOne_cfde9b8cac77
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_vandermondePsumOne_cfde9b8cac77
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:35:23.779617+00:00
-- url     : https://prove2.me/theorems/46aa58a3-da65-4780-88ea-a3133b5229bf
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb inh vandermonde Psum One cfde9b8cac77: P2 M Ground Theory Heights  Heights Rest Terms Comb inh vandermonde Psum One cfde9b8cac77
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb inh vandermonde Psum One cfde9b8cac77 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb inh vandermonde Psum One cfde9b8cac77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsComb.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsComb.lean#L56-L58

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_vandermondePsumOne_cfde9b8cac77 :
    ∑ i, (![2, 0] : Fin 2 → ℕ) i = ∑ i, stair 2 i + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«inh_vandermondePsumOne» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_vandermondePsumOne_cfde9b8cac77
