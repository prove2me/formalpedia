-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hypotheses_example_aa81192740bc
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hypotheses_example_aa81192740bc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:17.821084+00:00
-- url     : https://prove2.me/theorems/551a9a4f-106f-4d99-8fcb-bce9d630340c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hypotheses example aa81192740bc: P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hypotheses example aa81192740bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hypotheses example aa81192740bc construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cut Regular hypotheses example aa81192740bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L205-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L205-L211

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hypotheses_example_aa81192740bc :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = ((0 + 1 : ℕ)) ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«CutRegular».«hypotheses_example» := P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hypotheses_example_aa81192740bc
