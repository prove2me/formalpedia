-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eventualValue_eq_zero_39edb4ed1474
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eventualValue_eq_zero_39edb4ed1474
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:38:50.388799+00:00
-- url     : https://prove2.me/theorems/0e596147-dc1f-4f25-baf0-4d8adad10da2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular eventual Value eq zero 39edb4ed1474: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular eventual Value eq zero 39edb4ed1474
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular eventual Value eq zero 39edb4ed1474 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular eventual Value eq zero 39edb4ed1474 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L41-L47

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eventualValue_eq_zero_39edb4ed1474 {f : (K → ℤ) → ℤ} (hf : ∀ᶠ m in Filter.atTop, f m = 0) :
    eventualValue f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«eventualValue_eq_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_eventualValue_eq_zero_39edb4ed1474
