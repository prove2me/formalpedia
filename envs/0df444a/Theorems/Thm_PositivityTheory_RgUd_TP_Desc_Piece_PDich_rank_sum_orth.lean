-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_rank_sum_orth
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.rank_sum_orth
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:02.354114+00:00
-- url     : https://prove2.me/theorems/268111aa-caaa-5dc2-be45-55dced35af84
-- title:
--   PDich: rank sum orth
-- statement:
--   The PDich construction uses the rank sum orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/RankPosOfNe.lean#L44-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/RankPosOfNe.lean#L44-L61

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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.rank_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    (∑ i ∈ s, e i).rank = ∑ i ∈ s, (e i).rank := by sorry
