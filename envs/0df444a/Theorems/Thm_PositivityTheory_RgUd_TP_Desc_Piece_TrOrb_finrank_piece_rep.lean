-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_finrank_piece_rep
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.finrank_piece_rep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:21.704998+00:00
-- url     : https://prove2.me/theorems/666e8861-afd2-4e74-8e0d-cc3f380b4ad7
-- title:
--   Tr Orb: finrank piece rep
-- statement:
--   The Tr Orb construction uses the finrank piece rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbA.lean#L174-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbA.lean#L174-L182

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
universe u
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {N : ℕ}
variable (ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k)

theorem PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.finrank_piece_rep (e : A) : finrank k (piece (Rep ρ) e) = (ρ e).rank := by sorry
