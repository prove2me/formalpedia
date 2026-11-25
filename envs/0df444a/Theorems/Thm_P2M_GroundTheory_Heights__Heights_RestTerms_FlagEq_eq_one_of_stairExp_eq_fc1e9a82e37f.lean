-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_eq_one_of_stairExp_eq_fc1e9a82e37f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_eq_one_of_stairExp_eq_fc1e9a82e37f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:59.711358+00:00
-- url     : https://prove2.me/theorems/22531ec9-4a57-4042-a11b-974d176c29b9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq eq one of stair Exp eq fc1e9a82e37f: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq eq one of stair Exp eq fc1e9a82e37f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq eq one of stair Exp eq fc1e9a82e37f construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq eq one of stair Exp eq fc1e9a82e37f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L90-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L90-L99

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_eq_one_of_stairExp_eq_fc1e9a82e37f (w : Fin f → Equiv.Perm (Fin N)) (h : stairExp f N w = rho f N) :
    w = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«eq_one_of_stairExp_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_eq_one_of_stairExp_eq_fc1e9a82e37f
