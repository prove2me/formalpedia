-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eval_shiftPoly_461cf4c54608
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eval_shiftPoly_461cf4c54608
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:56.467002+00:00
-- url     : https://prove2.me/theorems/742700d6-7a0a-4b7b-ac04-e85f353fcc27
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eval shift Poly 461cf4c54608: P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eval shift Poly 461cf4c54608
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eval shift Poly 461cf4c54608 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eval shift Poly 461cf4c54608 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L23-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eval_shiftPoly_461cf4c54608 (b : K → ℤ) (p : MvPolynomial K ℚ) (x : K → ℚ) :
    eval x (shiftPoly b p) = eval (fun k => x k - b k) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MixedDiffConst».«eval_shiftPoly» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eval_shiftPoly_461cf4c54608
