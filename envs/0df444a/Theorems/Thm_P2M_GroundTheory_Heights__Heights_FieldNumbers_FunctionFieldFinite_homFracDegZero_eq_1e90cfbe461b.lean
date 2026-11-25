-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_homFracDegZero_eq_1e90cfbe461b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_homFracDegZero_eq_1e90cfbe461b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:18:16.001025+00:00
-- url     : https://prove2.me/theorems/b031d8ec-2f5c-5627-9747-5525bccd2552
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite hom Frac Deg Zero eq 1e90cfbe461b: P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite hom Frac Deg Zero eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite hom Frac Deg Zero eq 1e90cfbe461b construction uses the P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite hom Frac Deg Zero eq 1e90cfbe461b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PFunctionFieldFinite.lean#L31-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PFunctionFieldFinite.lean#L31-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFunctionFieldFinite
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
open GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_homFracDegZero_eq_1e90cfbe461b (hD : MChartDehomog.Statement.{u}) (P : Ideal (MRing ι F)) [P.IsPrime]
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    homFracDegZero P = IntermediateField.adjoin F (chartGens P u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«FunctionFieldFinite».«homFracDegZero_eq» := P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_homFracDegZero_eq_1e90cfbe461b
