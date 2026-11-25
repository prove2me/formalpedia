-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_idem_sum_orth
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.idem_sum_orth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:56.499014+00:00
-- url     : https://prove2.me/theorems/100e515b-d942-5543-b109-17b6f701a8d4
-- title:
--   PDich: idem sum orth
-- statement:
--   The PDich construction uses the idem sum orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/RankPosOfNe.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/RankPosOfNe.lean#L35-L42

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_RankPosOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
open Matrix
variable {k : Type} [Field k] {N : ℕ}

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.idem_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    IsIdempotentElem (∑ i ∈ s, e i) := by sorry
