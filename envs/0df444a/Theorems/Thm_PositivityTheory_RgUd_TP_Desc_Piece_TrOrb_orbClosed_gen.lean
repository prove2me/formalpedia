-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_orbClosed_gen
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.orbClosed_gen
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:36.171023+00:00
-- url     : https://prove2.me/theorems/ca32113a-e2ac-5899-a673-72ff1b6c31af
-- title:
--   Tr Orb: orb Closed gen
-- statement:
--   The Tr Orb construction uses the orb Closed gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbB.lean#L38-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbB.lean#L38-L115

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbB
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
variable {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {N : ℕ}

theorem PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.orbClosed_gen (N r : ℕ) (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (hA : IsReduced A)
    (b : Fin r → A) (hb : Submodule.span k (Set.range b) = ⊤) (ρ₀ : A →ₐ[k] Matrix (Fin N) (Fin N) k) :
    IsClosed {w : Fin r → Matrix (Fin N) (Fin N) k | ∃ g : GL (Fin N) k, ∀ i, w i = g.val * ρ₀ (b i) * g⁻¹.val} := by sorry
