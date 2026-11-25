-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_card_blkB
-- name    : PositivityTheory.Rg.Sw.LVs.dp_card_blkB
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:36.398586+00:00
-- url     : https://prove2.me/theorems/8df801d4-5d17-52a7-8706-cea4c4da1097
-- title:
--   LVs: dp card blk B
-- statement:
--   The LVs construction uses the dp card blk B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L374-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L374-L375

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.dp_card_blkB {j : ℕ} (hj : j ≤ n) : Fintype.card (blkB (n := n) j) = n - j := by sorry
