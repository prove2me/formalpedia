-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_UMGS_pr_succ
-- name    : PositivityTheory.ThKEst.UMGS.pr_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:51.471414+00:00
-- url     : https://prove2.me/theorems/53fd5d03-3c00-4d9e-a205-3799bcd6151b
-- title:
--   UMGS: pr succ
-- statement:
--   The UMGS construction uses the pr succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L65-L67

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
omit [TopologicalSpace G] [ContinuousMul G]

theorem PositivityTheory.ThKEst.UMGS.pr_succ {k : ℕ} (γ : Fin (k + 1) → (Multiplicative ℝ →* G)) (t : Fin (k + 1) → ℝ) :
    pr γ t = γ 0 (Multiplicative.ofAdd (t 0)) * pr (fun i => γ i.succ) (fun i => t i.succ) := by sorry
