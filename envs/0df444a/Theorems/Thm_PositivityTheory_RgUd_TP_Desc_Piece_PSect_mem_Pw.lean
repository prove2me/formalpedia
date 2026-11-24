-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_mem_Pw
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.mem_Pw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:56.285202+00:00
-- url     : https://prove2.me/theorems/965179ba-b3c9-4b8d-9063-f063a829d200
-- title:
--   PSect: mem Pw
-- statement:
--   The PSect construction uses the mem Pw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/MemPw.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/MemPw.lean#L21-L44

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_MemPw
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
open Module
variable {k : Type*} [Field k]

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.mem_Pw {B : Type*} [CommRing B] [Algebra k B] (p c : ℕ) [Fact p.Prime] [CharP k p]
    (hroot : ∀ a : k, ∃ w : B, w ^ (p ^ c) = algebraMap k B a) {b : B} :
    b ∈ Pw k B (p ^ c) ↔ ∃ w : B, w ^ (p ^ c) = b := by sorry
