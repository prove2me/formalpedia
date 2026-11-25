-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_series
-- name    : PositivityTheory.ThKEst.CS.Dual.series
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:18.979842+00:00
-- url     : https://prove2.me/theorems/289b9dd3-22a2-4827-9dfb-22412a202d91
-- title:
--   Dual: series
-- statement:
--   The Dual construction uses the series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L271-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L271-L309

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

theorem PositivityTheory.ThKEst.CS.Dual.series (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {P : G → ℂ} (hP : Continuous P)
    (hper : ∀ ξ u, P (r ξ + u) = P u) {c : Γ → ℂ} (hc : ∀ ξ, ∫ u in D, e ξ u * P u ∂μ = c ξ)
    (hsum : Summable fun ξ => ‖c ξ‖) : (μ.real D : ℂ) * P 0 = ∑' ξ, c ξ := by sorry
