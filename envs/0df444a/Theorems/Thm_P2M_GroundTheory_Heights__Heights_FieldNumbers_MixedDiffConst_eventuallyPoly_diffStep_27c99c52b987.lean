-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_diffStep_27c99c52b987
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_diffStep_27c99c52b987
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:09.095204+00:00
-- url     : https://prove2.me/theorems/6e894a2b-4b8e-418b-97f0-ef6c0f57cb1d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eventually Poly diff Step 27c99c52b987: P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eventually Poly diff Step
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eventually Poly diff Step 27c99c52b987 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eventually Poly diff Step 27c99c52b987 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L91-L98

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_diffStep_27c99c52b987 (b : K → ℤ) {g : (K → ℤ) → ℤ} {q : MvPolynomial K ℚ}
    (hq : EventuallyPoly g q) : EventuallyPoly (diffStep b g) (polyStep b q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MixedDiffConst».«eventuallyPoly_diffStep» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_diffStep_27c99c52b987
