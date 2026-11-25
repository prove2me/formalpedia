-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_esymm_mem_range_4f4cf4a0cb66
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_esymm_mem_range_4f4cf4a0cb66
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:59.951705+00:00
-- url     : https://prove2.me/theorems/85fe3072-d82a-4b0e-9a7d-1dbe104b1b85
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag esymm mem range 4f4cf4a0cb66: P2 M Ground Theory Heights  Heights Rest Terms Flag esymm mem range 4f4cf4a0cb66
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag esymm mem range 4f4cf4a0cb66 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag esymm mem range 4f4cf4a0cb66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L43-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L43-L63

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_esymm_mem_range_4f4cf4a0cb66 (N k : ℕ) (hk : k ≤ N) :
    esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«esymm_mem_range» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_esymm_mem_range_4f4cf4a0cb66
