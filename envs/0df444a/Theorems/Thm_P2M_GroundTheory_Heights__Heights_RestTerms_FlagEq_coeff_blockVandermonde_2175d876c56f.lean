-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_blockVandermonde_2175d876c56f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_blockVandermonde_2175d876c56f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:55.402905+00:00
-- url     : https://prove2.me/theorems/fc2114c6-5371-4b0b-a95d-334526b0555c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff block Vandermonde 2175d876c56f: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff block Vandermonde 2175d876c56f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff block Vandermonde 2175d876c56f construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq coeff block Vandermonde 2175d876c56f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L84-L88

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_blockVandermonde_2175d876c56f (α : Fin f × Fin N →₀ ℕ) :
    coeff α (blockVandermonde f N) =
      ∑ w, ((permSign f N w : ℤ) : ℚ) * if stairExp f N w = α then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«coeff_blockVandermonde» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_blockVandermonde_2175d876c56f
