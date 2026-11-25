-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_quotPiece_natCast_c8e9aee8bbc8
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_quotPiece_natCast_c8e9aee8bbc8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:23:29.918856+00:00
-- url     : https://prove2.me/theorems/47614dc7-a8a0-504d-b9de-8c29baf53be3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment quot Piece nat Cast c8e9aee8bbc8: P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment quot Piece nat Cast c8e9aee8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment quot Piece nat Cast c8e9aee8bbc8 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment quot Piece nat Cast c8e9aee8bbc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L104-L106

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_quotPiece_natCast_c8e9aee8bbc8 (J : Ideal (MRing ι F)) (a : K → ℕ) :
    quotPiece J (fun k => (a k : ℤ)) = gradedPiece J a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«HilbertIncrement».«quotPiece_natCast» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_quotPiece_natCast_c8e9aee8bbc8
