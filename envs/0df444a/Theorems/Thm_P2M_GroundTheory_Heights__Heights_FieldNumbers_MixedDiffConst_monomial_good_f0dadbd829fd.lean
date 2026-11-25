-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_good_f0dadbd829fd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_good_f0dadbd829fd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:59.158168+00:00
-- url     : https://prove2.me/theorems/1916e674-b108-418c-aa55-989cfac06cab
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const monomial good f0dadbd829fd: P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const monomial good f0dadbd829fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const monomial good f0dadbd829fd construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const monomial good f0dadbd829fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L30-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L30-L58

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_good_f0dadbd829fd (b : K → ℤ) (s : K →₀ ℕ) (a : ℚ) :
    (shiftPoly b (monomial s a)).totalDegree ≤ (monomial s a).totalDegree ∧
      (polyStep b (monomial s a) = 0 ∨
        (polyStep b (monomial s a)).totalDegree + 1 ≤ (monomial s a).totalDegree) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MixedDiffConst».«monomial_good» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_good_f0dadbd829fd
