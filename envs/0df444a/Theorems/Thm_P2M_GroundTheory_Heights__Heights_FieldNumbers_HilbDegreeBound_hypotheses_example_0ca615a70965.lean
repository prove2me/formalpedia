-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_hypotheses_example_0ca615a70965
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_hypotheses_example_0ca615a70965
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:00.174351+00:00
-- url     : https://prove2.me/theorems/8e83222f-835b-4a0f-8528-b8641ae5364e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Degree Bound hypotheses example 0ca615a70965: P2 M Ground Theory Heights  Heights Field Numbers Hilb Degree Bound hypotheses example 0ca615a70965
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Degree Bound hypotheses example 0ca615a70965 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Degree Bound hypotheses example 0ca615a70965 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L174-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L174-L181

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_hypotheses_example_0ca615a70965 :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsRelevant (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) ∧
      (X () + 1 : MvPolynomial Unit ℚ) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbDegreeBound».«hypotheses_example» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_hypotheses_example_0ca615a70965
