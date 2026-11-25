-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_rank_pos_of_ne
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.rank_pos_of_ne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:12.665828+00:00
-- url     : https://prove2.me/theorems/6fa9b8b9-45b4-4a1e-bee7-e03ed22d6590
-- title:
--   PDich: rank pos of ne
-- statement:
--   The PDich construction uses the rank pos of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/RankPosOfNe.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/RankPosOfNe.lean#L63-L69

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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.rank_pos_of_ne {e : Matrix (Fin N) (Fin N) k} (h : e ≠ 0) : 0 < e.rank := by sorry
