-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_map_d80caa80bd95
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_map_d80caa80bd95
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:21.175984+00:00
-- url     : https://prove2.me/theorems/91655f52-6ea6-4c78-bea9-fb658520d77d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finrank graded Piece map d80caa80bd95: P2 M Ground Theory Heights  Heights Field Numbers finrank graded Piece map d80caa80bd95
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finrank graded Piece map d80caa80bd95 construction uses the P2 M Ground Theory Heights  Heights Field Numbers finrank graded Piece map d80caa80bd95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L196-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L196-L258

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_map_d80caa80bd95 (I : Ideal (MRing ι F)) (m : K → ℕ) :
    Module.finrank F' (gradedPiece (I.map (map (algebraMap F F'))) m) =
      Module.finrank F (gradedPiece I m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finrank_gradedPiece_map» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_map_d80caa80bd95
