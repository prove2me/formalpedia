-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_component_mul_form_2d063eda04f4
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_component_mul_form_2d063eda04f4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:37.000812+00:00
-- url     : https://prove2.me/theorems/67eda84f-ea03-4da1-8666-af91b7fc1185
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide component mul form 2d063eda04f4: P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide component mul form 2d063eda04f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide component mul form 2d063eda04f4 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide component mul form 2d063eda04f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L22-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_component_mul_form_2d063eda04f4 {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c)
    (t : MRing ι F) (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (t * s) =
      if c ≤ n then weightedHomogeneousComponent (blockWeight ι) (n - c) t * s else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbExactDivide».«component_mul_form» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_component_mul_form_2d063eda04f4
