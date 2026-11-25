-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_UMGS_exists_partial
-- name    : PositivityTheory.ThKEst.UMGS.exists_partial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:22.138112+00:00
-- url     : https://prove2.me/theorems/0e33e86d-b819-4b5d-af70-6873e3a0ecae
-- title:
--   UMGS: exists partial
-- statement:
--   The UMGS construction uses the exists partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L125-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L125-L153

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

theorem PositivityTheory.ThKEst.UMGS.exists_partial (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G)) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L)
    (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y) (n : WithTop ℕ∞) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, γ i ∈ L) →
    ∀ i, ∃ Z : (Fin k → ℝ) → ι → A, ContDiff ℝ n Z ∧ ∀ t, ∃ γ' ∈ L, Gn m γ' (Z t) ∧
      ∀ s, pr γ (update t i (t i + s)) = pr γ t * γ' (Multiplicative.ofAdd s) := by sorry
