-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fl_step
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_step
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:01.251341+00:00
-- url     : https://prove2.me/theorems/dea8faf3-87e2-4392-85f0-e5beba096dce
-- title:
--   PSect: fl step
-- statement:
--   The PSect construction uses the fl step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/CompIterateFrobenius.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/CompIterateFrobenius.lean#L9-L30

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
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
open Module Polynomial IntermediateField

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_step {F E : Type*} [Field F] [Field E] [Algebra F E] (p : ℕ) [hp : Fact p.Prime]
    [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E))
    (L : IntermediateField F E) {x : E} (hx : x ∉ L) :
    finrank L (adjoin L {x}) = p := by sorry
