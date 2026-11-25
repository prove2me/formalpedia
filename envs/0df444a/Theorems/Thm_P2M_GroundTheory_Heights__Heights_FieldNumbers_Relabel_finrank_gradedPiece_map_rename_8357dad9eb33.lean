-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_finrank_gradedPiece_map_rename_8357dad9eb33
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_finrank_gradedPiece_map_rename_8357dad9eb33
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:29.712801+00:00
-- url     : https://prove2.me/theorems/b414d1dc-d0c9-4193-a3d4-e9926e3d3242
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Relabel finrank graded Piece map rename 8357dad9eb33: P2 M Ground Theory Heights  Heights Field Numbers Relabel finrank graded Piece map rename 8357da
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Relabel finrank graded Piece map rename 8357dad9eb33 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Relabel finrank graded Piece map rename 8357dad9eb33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L119-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
variable {K₁ K₂ : Type*} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*}
  (e : K₁ ≃ K₂) (φ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hφ : ∀ v, (φ v).1 = e v.1)
  {F : Type*} [Field F]
include hφ

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_finrank_gradedPiece_map_rename_8357dad9eb33 (I : Ideal (MRing ι₁ F)) (d : K₂ → ℕ) :
    Module.finrank F (gradedPiece (I.map (renameEquiv F φ)) d) =
      Module.finrank F (gradedPiece I (d ∘ e)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«Relabel».«finrank_gradedPiece_map_rename» := P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_finrank_gradedPiece_map_rename_8357dad9eb33
