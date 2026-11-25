-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_W_rank_iff_det
-- name    : PositivityTheory.ThKEst.W.rank_iff_det
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:23.690101+00:00
-- url     : https://prove2.me/theorems/5fcb1a9f-d3d9-4def-a0e0-5d4767b73792
-- title:
--   W: rank iff det
-- statement:
--   The W construction uses the rank iff det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L35-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology GlobalTheory.WeilM
open scoped Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.W
variable {k : Type} [Field k] {n d : ℕ}

theorem PositivityTheory.ThKEst.W.rank_iff_det (Y : Matrix (Fin n) (Fin d) k) : Y.rank = n ↔ ∃ C : Matrix (Fin d) (Fin n) k, (Y * C).det ≠ 0 := by sorry
