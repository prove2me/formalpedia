-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_hypotheses_example_499b36c3f9ca
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_hypotheses_example_499b36c3f9ca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:35.223874+00:00
-- url     : https://prove2.me/theorems/cd6d4711-4fc5-4e06-aa29-08d7f447ee2d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide hypotheses example 499b36c3f9ca: P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide hypotheses example 499b36c3f9ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide hypotheses example 499b36c3f9ca construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide hypotheses example 499b36c3f9ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L151-L154

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_hypotheses_example_499b36c3f9ca :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbExactDivide».«hypotheses_example» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_hypotheses_example_499b36c3f9ca
