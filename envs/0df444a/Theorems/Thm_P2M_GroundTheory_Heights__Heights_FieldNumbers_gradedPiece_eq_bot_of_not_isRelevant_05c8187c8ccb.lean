-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_bot_of_not_isRelevant_05c8187c8ccb
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_bot_of_not_isRelevant_05c8187c8ccb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:46.399015+00:00
-- url     : https://prove2.me/theorems/babf6dc4-8afd-439f-8aa8-61045f48a8a4
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers graded Piece eq bot of not is Relevant 05c8187c8ccb: P2 M Ground Theory Heights  Heights Field Numbers graded Piece eq bot of not is Relevant 05c8187c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers graded Piece eq bot of not is Relevant 05c8187c8ccb construction uses the P2 M Ground Theory Heights  Heights Field Numbers graded Piece eq bot of not is Relevant 05c8187c8ccb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbIrrelevantZero.lean#L38-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbIrrelevantZero.lean#L38-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbIrrelevantZero
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
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_bot_of_not_isRelevant_05c8187c8ccb {I : Ideal (MRing ι F)} (hI : ¬ IsRelevant I)
    {m : K → ℕ} (hm : ∀ k, 1 ≤ m k) : gradedPiece I m = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«gradedPiece_eq_bot_of_not_isRelevant» := P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_bot_of_not_isRelevant_05c8187c8ccb
