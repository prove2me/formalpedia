-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_le_of_height_add_0297706b95e3
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_le_of_height_add_0297706b95e3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:38:56.050739+00:00
-- url     : https://prove2.me/theorems/af8e3fc1-c0e1-5e23-ae50-ff47f5d98246
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular le of height add 0297706b95e3: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular le of height add 0297706b95e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular le of height add 0297706b95e3 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular le of height add 0297706b95e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L185-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L185-L202

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_le_of_height_add_0297706b95e3 {h : ℕ∞} {x : WithBot ℕ∞} {e : ℕ} (hh : h ≤ 1)
    (hsum : (h : WithBot ℕ∞) + x = ((e + 1 : ℕ) : WithBot ℕ∞)) : ((e : ℕ) : WithBot ℕ∞) ≤ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«le_of_height_add» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_le_of_height_add_0297706b95e3
