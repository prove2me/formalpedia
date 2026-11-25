-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_orth
-- name    : PositivityTheory.ThKEst.CS.Dual.orth
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:42.015682+00:00
-- url     : https://prove2.me/theorems/6fff6b0a-23cb-4f43-a2e4-952253195dc1
-- title:
--   Dual: orth
-- statement:
--   The Dual construction uses the orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L256-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L256-L269

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

theorem PositivityTheory.ThKEst.CS.Dual.orth (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {ξ : Γ} (hξ : ξ ≠ 0) :
    ∫ u in D, e ξ u ∂μ = 0 := by sorry
