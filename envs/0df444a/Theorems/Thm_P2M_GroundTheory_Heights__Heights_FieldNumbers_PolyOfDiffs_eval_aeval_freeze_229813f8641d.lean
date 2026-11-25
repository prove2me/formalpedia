-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_freeze_229813f8641d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_freeze_229813f8641d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:17.524226+00:00
-- url     : https://prove2.me/theorems/adda9944-b826-4c57-9257-6fc9d13649e0
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs eval aeval freeze 229813f8641d: P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs eval aeval freeze 229813f8641d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs eval aeval freeze 229813f8641d construction uses the P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs eval aeval freeze 229813f8641d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L110-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L110-L117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
variable {K : Type}
variable [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_freeze_229813f8641d (s : Finset K) (N x : K → ℚ) (P : MvPolynomial K ℚ) :
    eval x (aeval (freeze s N) P) = eval (fun j => if j ∈ s then x j else N j) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PolyOfDiffs».«eval_aeval_freeze» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_freeze_229813f8641d
