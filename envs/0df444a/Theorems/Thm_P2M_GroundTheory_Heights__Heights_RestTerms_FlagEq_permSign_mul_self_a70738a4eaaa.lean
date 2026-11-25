-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_mul_self_a70738a4eaaa
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_mul_self_a70738a4eaaa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:07.117476+00:00
-- url     : https://prove2.me/theorems/6e6ec14b-365d-59b2-8e0b-6c564609a4ff
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq perm Sign mul self a70738a4eaaa: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq perm Sign mul self a70738a4eaaa
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq perm Sign mul self a70738a4eaaa construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq perm Sign mul self a70738a4eaaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L41-L44

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_mul_self_a70738a4eaaa (u : Fin f → Equiv.Perm (Fin N)) :
    permSign f N u * permSign f N u = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«permSign_mul_self» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_mul_self_a70738a4eaaa
