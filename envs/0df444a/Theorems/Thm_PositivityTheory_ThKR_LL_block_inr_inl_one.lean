-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_block_inr_inl_one
-- name    : PositivityTheory.ThKR.LL.block_inr_inl_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:47:22.875071+00:00
-- url     : https://prove2.me/theorems/e67dea9c-3193-4df7-96c5-9127091a90dd
-- title:
--   LL: block inr inl one
-- statement:
--   The LL construction uses the block inr inl one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L41-L43

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.LL.block_inr_inl_one : bl Sum.inr Sum.inl (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 0 := by sorry
