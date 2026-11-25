-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_rank_add_orth
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.rank_add_orth
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:08.025804+00:00
-- url     : https://prove2.me/theorems/feb547a2-80e9-42e2-894e-47fae329f822
-- title:
--   PDich: rank add orth
-- statement:
--   The PDich construction uses the rank add orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/RankPosOfNe.lean#L9-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/RankPosOfNe.lean#L9-L33

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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.rank_add_orth {a b : Matrix (Fin N) (Fin N) k} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b = 0) (hba : b * a = 0) : (a + b).rank = a.rank + b.rank := by sorry
