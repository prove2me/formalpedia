-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_inv_6fdc7c5857e5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_inv_6fdc7c5857e5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:17.963292+00:00
-- url     : https://prove2.me/theorems/fff95834-ba87-4667-9f38-287e0ce0a897
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq perm Sign inv 6fdc7c5857e5: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq perm Sign inv 6fdc7c5857e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq perm Sign inv 6fdc7c5857e5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq perm Sign inv 6fdc7c5857e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L34-L35

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_inv_6fdc7c5857e5 (w : Fin f → Equiv.Perm (Fin N)) : permSign f N w⁻¹ = permSign f N w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«permSign_inv» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_inv_6fdc7c5857e5
