-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_top_234e7946562e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_top_234e7946562e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:38:38.068369+00:00
-- url     : https://prove2.me/theorems/86f912ee-82ec-4b61-8570-f2c3d3cbe0eb
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hilb Fn top 234e7946562e: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hilb Fn top 234e7946562e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hilb Fn top 234e7946562e construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hilb Fn top 234e7946562e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRegular.lean#L54-L65

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_top_234e7946562e (m : K → ℤ) : hilbFn (⊤ : Ideal (MRing ι F)) m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«hilbFn_top» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_top_234e7946562e
