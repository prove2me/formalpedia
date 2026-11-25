-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_ringPiece_natCast_788d1e277de0
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_ringPiece_natCast_788d1e277de0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:54.278794+00:00
-- url     : https://prove2.me/theorems/bd47c64c-c827-40a8-a309-e2bc8cabc65f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment ring Piece nat Cast 788d1e277de0: P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment ring Piece nat Cast 788d1e27
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment ring Piece nat Cast 788d1e277de0 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment ring Piece nat Cast 788d1e277de0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L42-L47

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_ringPiece_natCast_788d1e277de0 (a : K → ℕ) :
    ringPiece (F := F) (ι := ι) (fun k => (a k : ℤ)) =
      weightedHomogeneousSubmodule F (blockWeight ι) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«HilbertIncrement».«ringPiece_natCast» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_ringPiece_natCast_788d1e277de0
