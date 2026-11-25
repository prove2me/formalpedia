-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_sq_sum_lt
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.sq_sum_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:32.378795+00:00
-- url     : https://prove2.me/theorems/94d7ccb7-fe99-4a8e-9b18-d3dc05d255d2
-- title:
--   PDich: sq sum lt
-- statement:
--   The PDich construction uses the sq sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/SqSumLe.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/SqSumLe.lean#L12-L23

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_SqSumLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.sq_sum_lt {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i) (h : 1 < s.card) :
    ∑ i ∈ s, m i ^ 2 < (∑ i ∈ s, m i) ^ 2 := by sorry
