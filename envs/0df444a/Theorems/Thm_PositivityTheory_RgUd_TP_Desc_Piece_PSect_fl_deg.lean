-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fl_deg
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_deg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:03.65664+00:00
-- url     : https://prove2.me/theorems/da1fa053-04a1-408f-968e-2f068eb8b72c
-- title:
--   PSect: fl deg
-- statement:
--   The PSect construction uses the fl deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/FieldGen.lean#L10-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/FieldGen.lean#L10-L52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_MemPw
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_FieldGen
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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_deg {k E : Type*} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [CharP E p]
    (hroot : ∀ a : k, ∃ w : E, w ^ (p ^ c) = algebraMap k E a) :
    (Pj E p c).relfinrank ⊤ = finrank k (Tw k p c) := by sorry
