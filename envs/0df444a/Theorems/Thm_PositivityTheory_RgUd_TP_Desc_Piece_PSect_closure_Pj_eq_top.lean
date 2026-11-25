-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_closure_Pj_eq_top
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PSect.closure_Pj_eq_top
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:17.908705+00:00
-- url     : https://prove2.me/theorems/3c73f8de-3eeb-4500-a1b5-01f5a4dd3980
-- title:
--   PSect: closure Pj eq top
-- statement:
--   The PSect construction uses the closure Pj eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/CompIterateFrobenius.lean#L117-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/CompIterateFrobenius.lean#L117-L138

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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PSect.closure_Pj_eq_top {S : Set E} (hS : Subfield.closure ((Pj E p 1 : Set E) ∪ S) = ⊤)
    (j : ℕ) : Subfield.closure ((Pj E p j : Set E) ∪ S) = ⊤ := by sorry
