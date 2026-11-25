-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_X_223dfec544ec
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_X_223dfec544ec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:28.895314+00:00
-- url     : https://prove2.me/theorems/4caffe3e-0b6d-4372-992f-b83c4a0528ee
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs eval aeval X 223dfec544ec: P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs eval aeval X 223dfec544ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs eval aeval X 223dfec544ec construction uses the P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs eval aeval X 223dfec544ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L47-L52

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_X_223dfec544ec (y : K → ℚ) (k : K) (F : Polynomial ℚ) :
    eval y (Polynomial.aeval (X k) F) = F.eval (y k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PolyOfDiffs».«eval_aeval_X» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_X_223dfec544ec
