-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_finrank_gradedPiece_f3564c8558b5
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_finrank_gradedPiece_f3564c8558b5
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:20.960965+00:00
-- url     : https://prove2.me/theorems/f311603a-80d6-4fef-bef1-29b35ad98beb
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num finrank graded Piece f3564c8558b5: P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num finrank graded Piece f3564c8558b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num finrank graded Piece f3564c8558b5 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num finrank graded Piece f3564c8558b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConjIntNum.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConjIntNum.lean#L66-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum
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
open MvPolynomial NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_finrank_gradedPiece_f3564c8558b5 (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) :
    Module.finrank F (gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m) =
      Module.finrank F (gradedPiece J m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConjIntNum».«finrank_gradedPiece» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_finrank_gradedPiece_f3564c8558b5
