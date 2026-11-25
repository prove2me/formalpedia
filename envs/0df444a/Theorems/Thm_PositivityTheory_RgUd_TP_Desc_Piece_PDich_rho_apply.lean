-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_rho_apply
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.rho_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:30.32907+00:00
-- url     : https://prove2.me/theorems/70627c59-bc6a-4819-a216-0119cce81153
-- title:
--   PDich: rho apply
-- statement:
--   The PDich construction uses the rho apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/ToMatrixMulVec.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/ToMatrixMulVec.lean#L47-L48

import Mathlib
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
variable {k : Type} [Field k] {N : ℕ}
variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.rho_apply (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) (a : A) (w : Wd e) :
    ((rho hA he a w : Wd e) : Fin N → k) = a.1 *ᵥ (w : Fin N → k) := by sorry
