-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_W_rank_neg_full
-- name    : PositivityTheory.ThKEst.W.rank_neg_full
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:51:14.969091+00:00
-- url     : https://prove2.me/theorems/0c2c09a8-bea9-4b96-9327-8da666f0ddda
-- title:
--   W: rank neg full
-- statement:
--   The W construction uses the rank neg full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L51-L53

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

theorem PositivityTheory.ThKEst.W.rank_neg_full {Y : Matrix (Fin n) (Fin d) k} (h : (-Y).rank = n) : Y.rank = n := by sorry
