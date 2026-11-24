-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_W_rank_iff_right
-- name    : PositivityTheory.ThKEst.W.rank_iff_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:54:01.333973+00:00
-- url     : https://prove2.me/theorems/1dd76f12-48ef-46d5-a88c-47c5025eb93a
-- title:
--   W: rank iff right
-- statement:
--   The W construction uses the rank iff right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L13-L33

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

theorem PositivityTheory.ThKEst.W.rank_iff_right (Y : Matrix (Fin n) (Fin d) k) : Y.rank = n ↔ ∃ C : Matrix (Fin d) (Fin n) k, Y * C = 1 := by sorry
