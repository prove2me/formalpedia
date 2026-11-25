-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_W_isOpen_rank
-- name    : PositivityTheory.ThKEst.W.isOpen_rank
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:25.715942+00:00
-- url     : https://prove2.me/theorems/7e8e3185-861a-445e-9cdb-8967631cec5c
-- title:
--   W: is Open rank
-- statement:
--   The W construction uses the is Open rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L79-L87

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

theorem PositivityTheory.ThKEst.W.isOpen_rank [TopologicalSpace k] [IsTopologicalRing k] [T1Space k] :
    IsOpen {Y : Matrix (Fin n) (Fin d) k | Y.rank = n} := by sorry
