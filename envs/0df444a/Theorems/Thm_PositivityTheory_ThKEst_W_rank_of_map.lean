-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_W_rank_of_map
-- name    : PositivityTheory.ThKEst.W.rank_of_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:37.327032+00:00
-- url     : https://prove2.me/theorems/ffc754a2-162b-499c-a2ac-8404611fec89
-- title:
--   W: rank of map
-- statement:
--   The W construction uses the rank of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L55-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L55-L77

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

theorem PositivityTheory.ThKEst.W.rank_of_map {E : Type} [Field E] (t : E →+* k) (x : Matrix (Fin n) (Fin d) E) (h : (x.map t).rank = n) :
    x.rank = n := by sorry
