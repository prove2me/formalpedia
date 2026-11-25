-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_blockVandermonde_eq_sum_53f79364cc46
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_blockVandermonde_eq_sum_53f79364cc46
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:32.227783+00:00
-- url     : https://prove2.me/theorems/e904c444-9d31-45f7-a00b-5f12abe65713
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq block Vandermonde eq sum 53f79364cc46: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq block Vandermonde eq sum 53f79364cc46
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq block Vandermonde eq sum 53f79364cc46 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq block Vandermonde eq sum 53f79364cc46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L69-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
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
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq
variable {f N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_blockVandermonde_eq_sum_53f79364cc46 (f N : ℕ) :
    blockVandermonde f N = ∑ w : Fin f → Equiv.Perm (Fin N),
      ((permSign f N w : ℤ) : ℚ) • monomial (stairExp f N w) (1 : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«blockVandermonde_eq_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_blockVandermonde_eq_sum_53f79364cc46
