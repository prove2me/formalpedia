-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_finrank_gradedPiece_348cd7d65ded
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_finrank_gradedPiece_348cd7d65ded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:51.863444+00:00
-- url     : https://prove2.me/theorems/42f8e36e-03be-4525-9699-a6789c50c06a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block finrank graded Piece 348cd7d65ded: P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block finrank graded Piece 348cd7d65ded
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block finrank graded Piece 348cd7d65ded construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Add Block finrank graded Piece 348cd7d65ded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L150-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbAddBlock.lean#L150-L242

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
variable {K : Type} [DecidableEq K] {ι : K → Type} {N : ℕ}
variable {F : Type u} [Field F]
variable [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_finrank_gradedPiece_348cd7d65ded (I : Ideal (MRing ι F)) (M : Option K → ℕ) :
    Module.finrank F (gradedPiece (addBlockPrime N I) M) =
      Module.finrank F (gradedPiece I (fun k => M (some k))) * (M none + N).choose N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbAddBlock».«finrank_gradedPiece» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_finrank_gradedPiece_348cd7d65ded
