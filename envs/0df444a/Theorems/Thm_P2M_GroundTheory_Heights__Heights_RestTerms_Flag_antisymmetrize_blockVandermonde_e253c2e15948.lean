-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_antisymmetrize_blockVandermonde_e253c2e15948
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_antisymmetrize_blockVandermonde_e253c2e15948
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:50.725827+00:00
-- url     : https://prove2.me/theorems/cd528d3e-05c0-4afb-8181-6e66917db14a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag antisymmetrize block Vandermonde e253c2e15948: P2 M Ground Theory Heights  Heights Rest Terms Flag antisymmetrize block Vandermonde e253c2e15948
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag antisymmetrize block Vandermonde e253c2e15948 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag antisymmetrize block Vandermonde e253c2e15948 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L105-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_antisymmetrize_blockVandermonde_e253c2e15948 (f N : ℕ) :
    antisymmetrize f N (blockVandermonde f N) =
      ((N.factorial : ℚ) ^ f) • blockVandermonde f N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«antisymmetrize_blockVandermonde» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_antisymmetrize_blockVandermonde_e253c2e15948
