-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_psum_mem_range_c0a256d7f214
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_psum_mem_range_c0a256d7f214
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:55.407002+00:00
-- url     : https://prove2.me/theorems/dca13a57-f1bb-42a0-9c79-aced9b3591a5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag psum mem range c0a256d7f214: P2 M Ground Theory Heights  Heights Rest Terms Flag psum mem range c0a256d7f214
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag psum mem range c0a256d7f214 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag psum mem range c0a256d7f214 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L34-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_psum_mem_range_c0a256d7f214 (N j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    psum (Fin N) ℚ j ∈ (powerSumHom N).range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«psum_mem_range» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_psum_mem_range_c0a256d7f214
