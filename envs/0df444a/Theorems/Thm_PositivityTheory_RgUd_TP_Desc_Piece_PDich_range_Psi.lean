-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_range_Psi
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.range_Psi
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:04:43.743632+00:00
-- url     : https://prove2.me/theorems/f4ad6b71-9d3f-401a-841b-54cc57c5fa11
-- title:
--   PDich: range Psi
-- statement:
--   The PDich construction uses the range Psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/PsiMulVec.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/PsiMulVec.lean#L43-L65

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FeIsField
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_PsiMulVec
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
  (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.range_Psi (hid : IsIdempotentElem e) :
    LinearMap.range (Psi hA he) =
      (Subalgebra.centralizer k (A : Set (Matrix (Fin N) (Fin N) k))).toSubmodule.map (LinearMap.mulLeft k e) := by sorry
