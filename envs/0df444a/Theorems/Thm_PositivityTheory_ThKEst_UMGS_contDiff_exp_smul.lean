-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_UMGS_contDiff_exp_smul
-- name    : PositivityTheory.ThKEst.UMGS.contDiff_exp_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:05.178902+00:00
-- url     : https://prove2.me/theorems/c7da227f-0485-438d-b205-f7d909120c38
-- title:
--   UMGS: cont Diff exp smul
-- statement:
--   The UMGS construction uses the cont Diff exp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L85-L88

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.UMGS
open Filter Topology Function
variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {ι : Type} [Fintype ι]

theorem PositivityTheory.ThKEst.UMGS.contDiff_exp_smul (Y : A) (n : WithTop ℕ∞) : ContDiff ℝ n fun t : ℝ => NormedSpace.exp (t • Y) := by sorry
