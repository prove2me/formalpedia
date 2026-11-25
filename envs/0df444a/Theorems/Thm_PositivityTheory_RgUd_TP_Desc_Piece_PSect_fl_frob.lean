-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fl_frob
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_frob
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:45.136794+00:00
-- url     : https://prove2.me/theorems/3400e03c-b979-4ec3-afd1-b5b4e9e3aba5
-- title:
--   PSect: fl frob
-- statement:
--   The PSect construction uses the fl frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/CompIterateFrobenius.lean#L140-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/CompIterateFrobenius.lean#L140-L162

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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_frob (c : ℕ) (hc : 0 < c) (hfin : (Pj E p c).relfinrank ⊤ ≠ 0) :
    ∃ n, (Pj E p c).relfinrank ⊤ = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Subfield.closure ((Pj E p c : Set E) ∪ Set.range α) = ⊤ := by sorry
