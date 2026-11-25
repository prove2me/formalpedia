-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_relfinrank_Pj
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.relfinrank_Pj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:49.761546+00:00
-- url     : https://prove2.me/theorems/0bc00697-7e7d-5ac5-a761-4063d2cad7f0
-- title:
--   PSect: relfinrank Pj
-- statement:
--   The PSect construction uses the relfinrank Pj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/CompIterateFrobenius.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/CompIterateFrobenius.lean#L109-L115

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
variable {E : Type*} [Field E] (p : ℕ) [hp : Fact p.Prime] [CharP E p]

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.relfinrank_Pj (j : ℕ) :
    (Pj E p j).relfinrank ⊤ = ((Pj E p 1).relfinrank ⊤) ^ j := by sorry
