-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaContracted_hypotheses_example_9fbe5bc3ae39
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaContracted_hypotheses_example_9fbe5bc3ae39
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:57.58023+00:00
-- url     : https://prove2.me/theorems/0d9a6711-85ba-4893-9d19-176ad42ab8e2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Projection Formula Contracted hypotheses example 9fbe5bc3ae39: P2 M Ground Theory Heights  Heights Field Numbers Projection Formula Contracted hypothe
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Projection Formula Contracted hypotheses example 9fbe5bc3ae39 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Projection Formula Contracted hypotheses example 9fbe5bc3ae39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L230-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L230-L240

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaContracted_hypotheses_example_9fbe5bc3ae39 :
    IsMultiProjPrime (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ)) = (1 : ℕ) ∧
      relDim (contractPrime Function.Embedding.some
        (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ))) < (1 : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ProjectionFormulaContracted».«hypotheses_example» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaContracted_hypotheses_example_9fbe5bc3ae39
