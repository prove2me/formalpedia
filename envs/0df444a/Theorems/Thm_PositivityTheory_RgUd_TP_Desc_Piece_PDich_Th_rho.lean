-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_Th_rho
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.Th_rho
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:06.897004+00:00
-- url     : https://prove2.me/theorems/3c764f6d-3de9-53e6-b6ae-5eb2df5938c2
-- title:
--   PDich: Th rho
-- statement:
--   The PDich construction uses the Th rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FeIsField.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FeIsField.lean#L30-L33

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FeIsField
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
variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
variable (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.Th_rho (a : A) : Th e (rho hA he a) = e * a.1 := by sorry
