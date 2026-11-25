-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eq_of_add_one_le_of_le_9a68ecf72589
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eq_of_add_one_le_of_le_9a68ecf72589
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:02:47.180678+00:00
-- url     : https://prove2.me/theorems/e6c46913-2871-42d8-963a-55f3155b6c26
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular eq of add one le of le 9a68ecf72589: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular eq of add one le of le 9a68ecf72589
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular eq of add one le of le 9a68ecf72589 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular eq of add one le of le 9a68ecf72589 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L165-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L165-L183

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eq_of_add_one_le_of_le_9a68ecf72589 {x : WithBot ℕ∞} {e : ℕ}
    (h1 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) (h2 : ((e : ℕ) : WithBot ℕ∞) ≤ x) :
    x = ((e : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«eq_of_add_one_le_of_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eq_of_add_one_le_of_le_9a68ecf72589
