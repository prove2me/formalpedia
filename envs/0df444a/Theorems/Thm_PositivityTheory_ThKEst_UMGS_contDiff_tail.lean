-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_UMGS_contDiff_tail
-- name    : PositivityTheory.ThKEst.UMGS.contDiff_tail
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:58.194528+00:00
-- url     : https://prove2.me/theorems/489be1e7-b7e5-43e9-b747-6c1386374afb
-- title:
--   UMGS: cont Diff tail
-- statement:
--   The UMGS construction uses the cont Diff tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L90-L91

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

theorem PositivityTheory.ThKEst.UMGS.contDiff_tail (k : ℕ) (n : WithTop ℕ∞) : ContDiff ℝ n fun (t : Fin (k + 1) → ℝ) (i : Fin k) => t i.succ := by sorry
