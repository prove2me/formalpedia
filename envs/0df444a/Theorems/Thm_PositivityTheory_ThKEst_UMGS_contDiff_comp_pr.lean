-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_UMGS_contDiff_comp_pr
-- name    : PositivityTheory.ThKEst.UMGS.contDiff_comp_pr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:40.186436+00:00
-- url     : https://prove2.me/theorems/02731372-b4fc-489f-ad6c-82badc41ed0c
-- title:
--   UMGS: cont Diff comp pr
-- statement:
--   The UMGS construction uses the cont Diff comp pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L155-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L155-L182

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

theorem PositivityTheory.ThKEst.UMGS.contDiff_comp_pr [FiniteDimensional ℝ A] (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G))
    (hc : ∀ γ ∈ L, Continuous γ) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L) (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y)
    {r : ℕ} (β : Fin r → (Multiplicative ℝ →* G)) (c : Fin r → (ι → A) →ₗ[ℝ] ℝ) (hβ : ∀ j, β j ∈ L)
    (hl : ∀ (f : G → ℂ) (f' : Fin r → G → ℂ), (∀ j, Continuous (f' j) ∧
      ∀ h, HasDerivAt (fun t : ℝ => f (h * β j (Multiplicative.ofAdd t))) (f' j h) 0) → ∀ γ ∈ L, ∀ Y, Gn m γ Y →
      ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ j, (c j Y : ℂ) * f' j h) 0)
    (S : Set (G → ℂ)) (hS : ∀ f ∈ S, Continuous f ∧
      ∀ γ ∈ L, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0)
    {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (hγ : ∀ i, γ i ∈ L) (g : G) (n : ℕ) :
    ∀ f ∈ S, ContDiff ℝ n fun t => f (g * pr γ t) := by sorry
