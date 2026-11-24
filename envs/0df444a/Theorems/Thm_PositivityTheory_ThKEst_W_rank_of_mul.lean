-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_W_rank_of_mul
-- name    : PositivityTheory.ThKEst.W.rank_of_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:57.81569+00:00
-- url     : https://prove2.me/theorems/4fa8cd26-ab38-4177-b41b-2f9fab0bf1fb
-- title:
--   W: rank of mul
-- statement:
--   The W construction uses the rank of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L44-L49

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

theorem PositivityTheory.ThKEst.W.rank_of_mul (A : Matrix (Fin n) (Fin n) k) (Y : Matrix (Fin n) (Fin d) k) (B : Matrix (Fin d) (Fin d) k)
    (h : (A * Y * B).rank = n) : Y.rank = n := by sorry
