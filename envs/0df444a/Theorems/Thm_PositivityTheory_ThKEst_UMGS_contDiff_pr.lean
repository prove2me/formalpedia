-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_UMGS_contDiff_pr
-- name    : PositivityTheory.ThKEst.UMGS.contDiff_pr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:08.767843+00:00
-- url     : https://prove2.me/theorems/2da79508-cb90-4e61-8047-d5f9b6809612
-- title:
--   UMGS: cont Diff pr
-- statement:
--   The UMGS construction uses the cont Diff pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L94-L104

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
omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι]

theorem PositivityTheory.ThKEst.UMGS.contDiff_pr (m : ι → G →* A) (n : WithTop ℕ∞) (w : ι) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G),
    (∀ i, ∃ Y, Gn m (γ i) Y) → ContDiff ℝ n (fun t => m w (pr γ t)) ∧ ContDiff ℝ n (fun t => m w (pr γ t)⁻¹) := by sorry
