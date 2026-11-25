-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_rdata
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.rdata
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:28.437828+00:00
-- url     : https://prove2.me/theorems/e8693afb-f581-480f-a9ac-aa56ec4bdfec
-- title:
--   PSect: rdata
-- statement:
--   The PSect construction uses the rdata property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/Rdata.lean#L10-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/Rdata.lean#L10-L63

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_FinrankAdjoinPowLe
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_SEps
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_Rdata
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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.rdata {k R : Type*} [Field k] [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsPrincipalIdealRing R]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hnil : ∀ r : R, IsNilpotent r → r ^ (p ^ c) = 0)
    (hroot : ∀ a : k, ∃ w : R, w ^ (p ^ c) = algebraMap k R a) :
    ∃ (r : ℕ) (s : Fin r → R) (c' : Fin r → Fin r → Fin r → k) (u : Fin r → k) (ε : R) (m : ℕ)
      (κ : Fin m → Fin r → k),
      (∀ j j', s j * s j' = ∑ t, c' j j' t • s t) ∧ ∑ j, u j • s j = 1 ∧ ε ^ (p ^ c) = 0 ∧
      (∀ y : R, ∃ γ : Fin (p ^ c) → Fin r → k, y = ∑ l, ∑ j, γ l j • (s j * ε ^ (l : ℕ))) ∧
      (∀ t, IsIdempotentElem (∑ j, κ t j • s j)) ∧ (∑ t, ∑ j, κ t j • s j) = 1 ∧
      (∀ t t', t ≠ t' → (∑ j, κ t j • s j) * (∑ j, κ t' j • s j) = 0) ∧
      ∀ t (v : Fin r → k), (∑ j, v j • s j) * (∑ j, κ t j • s j) = 0 ∨
        ∃ w : R, (∑ j, v j • s j) * (∑ j, κ t j • s j) * w = ∑ j, κ t j • s j := by sorry
