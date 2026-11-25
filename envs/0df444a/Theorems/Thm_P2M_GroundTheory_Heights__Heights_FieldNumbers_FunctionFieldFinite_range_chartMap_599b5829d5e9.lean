-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_range_chartMap_599b5829d5e9
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_range_chartMap_599b5829d5e9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:05:18.279878+00:00
-- url     : https://prove2.me/theorems/0d2b1c18-b9bf-5096-9c63-f7ac92d40ac5
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite range chart Map 599b5829d5e9: P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite range chart Map 599b5829d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite range chart Map 599b5829d5e9 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Function Field Finite range chart Map 599b5829d5e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PFunctionFieldFinite.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PFunctionFieldFinite.lean#L27-L29

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
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_range_chartMap_599b5829d5e9 (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartMap P u).range = Algebra.adjoin F (chartGens P u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«FunctionFieldFinite».«range_chartMap» := P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_range_chartMap_599b5829d5e9
