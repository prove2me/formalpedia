-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_sectionEx
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.sectionEx
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:12.814323+00:00
-- url     : https://prove2.me/theorems/5734a117-5657-4d05-bbf6-66e316bf8262
-- title:
--   PSect: section Ex
-- statement:
--   The PSect construction uses the section Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/FinrankAdjoinPowLe.lean#L75-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/FinrankAdjoinPowLe.lean#L75-L230

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_FieldGen
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_FinrankAdjoinPowLe
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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.sectionEx {k R : Type*} [Field k] [CommRing R] [Algebra k R] [FiniteDimensional k R]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hnil : ∀ r : R, IsNilpotent r → r ^ (p ^ c) = 0)
    (hroot : ∀ a : k, ∃ w : R, w ^ (p ^ c) = algebraMap k R a) :
    ∃ S : Subalgebra k R, (∀ s ∈ S, IsNilpotent s → s = 0) ∧ ∀ r : R, ∃ s ∈ S, IsNilpotent (r - s) := by sorry
