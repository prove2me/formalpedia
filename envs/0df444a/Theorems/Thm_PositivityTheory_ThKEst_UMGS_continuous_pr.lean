-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_UMGS_continuous_pr
-- name    : PositivityTheory.ThKEst.UMGS.continuous_pr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:20.957957+00:00
-- url     : https://prove2.me/theorems/54425605-61f8-4484-aca8-ec6f129ea2a0
-- title:
--   UMGS: continuous pr
-- statement:
--   The UMGS construction uses the continuous pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L76-L83

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

theorem PositivityTheory.ThKEst.UMGS.continuous_pr (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, Continuous (γ i)) → Continuous (pr γ) := by sorry
