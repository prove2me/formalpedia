-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_poisson_le
-- name    : PositivityTheory.ThKEst.CS.Dual.poisson_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:30.125925+00:00
-- url     : https://prove2.me/theorems/1b4c976f-6d91-4a5d-b8b6-bea4e9eb9f0f
-- title:
--   Dual: poisson le
-- statement:
--   The Dual construction uses the poisson le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L311-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L311-L376

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.CS
variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]
variable {r : Γ →+ G} {e : Γ → G → ℂ}
variable [MeasurableSpace G] [BorelSpace G] [Countable Γ] {μ : Measure G} [μ.IsAddHaarMeasure] {D : Set G}

theorem PositivityTheory.ThKEst.CS.Dual.poisson_le [LocallyCompactSpace G] (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ H : G → ℂ, Continuous H →
      (∀ K : Set G, IsCompact K → ∃ b : Γ → ℝ, Summable b ∧ ∀ ξ, ∀ a ∈ K, ‖H (r ξ + a)‖ ≤ b ξ) →
      ‖∑' ξ, H (r ξ)‖ₑ ≤ ENNReal.ofReal c * ∑' ξ, ‖∫ u, e ξ u * H u ∂μ‖ₑ := by sorry
