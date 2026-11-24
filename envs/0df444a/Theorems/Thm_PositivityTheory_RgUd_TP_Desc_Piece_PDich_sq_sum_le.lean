-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_sq_sum_le
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.sq_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:09.876805+00:00
-- url     : https://prove2.me/theorems/83ea8b96-78f5-4a61-a567-edc92f68ee2d
-- title:
--   PDich: sq sum le
-- statement:
--   The PDich construction uses the sq sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/SqSumLe.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/SqSumLe.lean#L5-L10

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

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.sq_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) : ∑ i ∈ s, m i ^ 2 ≤ (∑ i ∈ s, m i) ^ 2 := by sorry
