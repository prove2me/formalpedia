-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_eventually_zero_of_not_relevant_ade284a05af1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_eventually_zero_of_not_relevant_ade284a05af1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:38:49.21483+00:00
-- url     : https://prove2.me/theorems/06de4abe-f36c-5cce-ae92-282c198da3b6
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hilb Fn eventually zero of not relevant ade284a05af1: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hilb Fn eventually zer
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hilb Fn eventually zero of not relevant ade284a05af1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hilb Fn eventually zero of not relevant ade284a05af1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L91-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L91-L108

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_eventually_zero_of_not_relevant_ade284a05af1 {I : Ideal (MRing ι F)} (hI : ¬ IsRelevant I) :
    ∀ᶠ m in Filter.atTop, hilbFn I m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«hilbFn_eventually_zero_of_not_relevant» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_eventually_zero_of_not_relevant_ade284a05af1
