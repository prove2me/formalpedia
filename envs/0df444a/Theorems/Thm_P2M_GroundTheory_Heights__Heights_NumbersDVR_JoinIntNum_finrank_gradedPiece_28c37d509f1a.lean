-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_finrank_gradedPiece_28c37d509f1a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_finrank_gradedPiece_28c37d509f1a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:43.225194+00:00
-- url     : https://prove2.me/theorems/08df13f5-4003-424f-9c23-7e2c119ee2bf
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num finrank graded Piece 28c37d509f1a: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num finrank graded Piece 28c37d509f1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num finrank graded Piece 28c37d509f1a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num finrank graded Piece 28c37d509f1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L200-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L200-L226

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_finrank_gradedPiece_28c37d509f1a (V : Ideal (MRing ι F)) (M : K ⊕ Unit → ℕ) :
    Module.finrank F (gradedPiece (V.map (rename (liftVar (ι := ι) ptIdx))) M) =
      Module.finrank F (gradedPiece V (restrictFirst M)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«finrank_gradedPiece» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_finrank_gradedPiece_28c37d509f1a
