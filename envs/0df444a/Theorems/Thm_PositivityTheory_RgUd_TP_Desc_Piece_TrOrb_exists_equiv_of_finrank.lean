-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_exists_equiv_of_finrank
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.exists_equiv_of_finrank
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:11.544332+00:00
-- url     : https://prove2.me/theorems/414621a3-912d-4a21-929a-285286df3468
-- title:
--   Tr Orb: exists equiv of finrank
-- statement:
--   The Tr Orb construction uses the exists equiv of finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbA.lean#L130-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbA.lean#L130-L152

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

theorem PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.exists_equiv_of_finrank {k A : Type*} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    [IsReduced A] (M M' : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M'] [FiniteDimensional k M]
    [FiniteDimensional k M']
    (h : ∀ e : A, IsIdempotentElem e → finrank k (piece M e) = finrank k (piece M' e)) :
    Nonempty (M ≃ₗ[A] M') := by sorry
