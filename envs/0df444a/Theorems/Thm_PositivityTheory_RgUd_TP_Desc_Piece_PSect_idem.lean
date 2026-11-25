-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_idem
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.idem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:59.075276+00:00
-- url     : https://prove2.me/theorems/62466166-e7cb-4b7a-9f38-7669880f1e8a
-- title:
--   PSect: idem
-- statement:
--   The PSect construction uses the idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/SEps.lean#L9-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/SEps.lean#L9-L58

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_SEps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.idem {k S : Type*} [Field k] [CommRing S] [Algebra k S] [FiniteDimensional k S] [IsReduced S] :
    ∃ (m : ℕ) (e : Fin m → S), (∀ t, IsIdempotentElem (e t)) ∧ ∑ t, e t = 1 ∧
      (∀ t t', t ≠ t' → e t * e t' = 0) ∧ ∀ t s, s * e t = 0 ∨ ∃ w, s * e t * w = e t := by sorry
