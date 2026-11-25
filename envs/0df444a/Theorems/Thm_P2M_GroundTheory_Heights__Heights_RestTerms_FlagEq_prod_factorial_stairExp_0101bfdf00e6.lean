-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_prod_factorial_stairExp_0101bfdf00e6
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_prod_factorial_stairExp_0101bfdf00e6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:27.09436+00:00
-- url     : https://prove2.me/theorems/b8304307-48bd-4a8a-a12f-5a89c3570771
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq prod factorial stair Exp 0101bfdf00e6: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq prod factorial stair Exp 0101bfdf00e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq prod factorial stair Exp 0101bfdf00e6 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq prod factorial stair Exp 0101bfdf00e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean#L101-L109

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_prod_factorial_stairExp_0101bfdf00e6 (w : Fin f → Equiv.Perm (Fin N)) :
    (stairExp f N w).prod (fun _ e => (e.factorial : ℝ)) = stairConst f N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«prod_factorial_stairExp» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_prod_factorial_stairExp_0101bfdf00e6
