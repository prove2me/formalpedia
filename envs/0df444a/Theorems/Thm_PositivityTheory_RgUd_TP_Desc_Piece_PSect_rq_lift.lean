-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_rq_lift
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.rq_lift
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:08.393647+00:00
-- url     : https://prove2.me/theorems/1befb3bc-9eaa-4adc-9a47-37c0fb11abc9
-- title:
--   PSect: rq lift
-- statement:
--   The PSect construction uses the rq lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/RqLift.lean#L132-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/RqLift.lean#L132-L165

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_RqLift
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
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.rq_lift {B : Type*} [Ring B] [Algebra k B] (ι : A →ₐ[k] B) (x : B) (hc : ∀ a, Commute (ι a) x)
    (χ : k[X]) (hχ : aeval x χ = 0) (q : ℕ)
    (hq : ∀ P : A[X], IsNilpotent (P.eval₂ ι.toRingHom x) → (P.eval₂ ι.toRingHom x) ^ q = 0) :
    ∃ ρ : Rq A χ q →ₐ[k] B, ∀ P : A[X], ρ (Ideal.Quotient.mk _ P) = P.eval₂ ι.toRingHom x := by sorry
