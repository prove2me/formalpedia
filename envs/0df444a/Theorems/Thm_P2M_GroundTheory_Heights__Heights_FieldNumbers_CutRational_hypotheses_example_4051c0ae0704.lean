-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_hypotheses_example_4051c0ae0704
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_hypotheses_example_4051c0ae0704
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:52.1198+00:00
-- url     : https://prove2.me/theorems/5845e9d3-d5ab-48c4-b3e0-0a5a1f44d94b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Rational hypotheses example 4051c0ae0704: P2 M Ground Theory Heights  Heights Field Numbers Cut Rational hypotheses example 4051c0ae0704
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Rational hypotheses example 4051c0ae0704 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Rational hypotheses example 4051c0ae0704 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L213-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L213-L223

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_hypotheses_example_4051c0ae0704 :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = 1 ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      IsMultiHomog (X ⟨(), 1⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      (X ⟨(), 1⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRational».«hypotheses_example» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_hypotheses_example_4051c0ae0704
