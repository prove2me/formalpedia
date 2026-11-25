-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_sum_eq_73cf2fba62b3
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_sum_eq_73cf2fba62b3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:19.818632+00:00
-- url     : https://prove2.me/theorems/4f0119bd-44d8-5ae5-a86c-5be781ce475a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const sum eq 73cf2fba62b3: P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const sum eq 73cf2fba62b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const sum eq 73cf2fba62b3 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const sum eq 73cf2fba62b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L60-L68

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_sum_eq_73cf2fba62b3 (b : K → ℤ) (p : MvPolynomial K ℚ) :
    shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (coeff v p)) ∧
      polyStep b p = ∑ v ∈ p.support, polyStep b (monomial v (coeff v p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MixedDiffConst».«sum_eq» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_sum_eq_73cf2fba62b3
