-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_Pe_smul
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.Pe_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:15.197651+00:00
-- url     : https://prove2.me/theorems/6ce8b750-0065-5f14-b0e3-0565bb839d44
-- title:
--   PDich: Pe smul
-- statement:
--   The PDich construction uses the Pe smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/PsiMulVec.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/PsiMulVec.lean#L28-L32

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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.Pe_smul (a : A) (v : Fin N → k) :
    Pe e (a.1 *ᵥ v) = (⟨rho hA he a, a, rfl⟩ : Fe hA he) • Pe e v := by sorry
