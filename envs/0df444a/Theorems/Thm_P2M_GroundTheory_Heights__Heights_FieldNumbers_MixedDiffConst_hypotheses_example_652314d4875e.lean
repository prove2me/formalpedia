-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_hypotheses_example_652314d4875e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_hypotheses_example_652314d4875e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:53.26618+00:00
-- url     : https://prove2.me/theorems/4fcb1fcc-715d-4fdd-8c33-d48dfc33956e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const hypotheses example 652314d4875e: P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const hypotheses example 652314d4875e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const hypotheses example 652314d4875e construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const hypotheses example 652314d4875e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L183-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L183-L188

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_hypotheses_example_652314d4875e :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsRelevant (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = (1 : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MixedDiffConst».«hypotheses_example» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_hypotheses_example_652314d4875e
