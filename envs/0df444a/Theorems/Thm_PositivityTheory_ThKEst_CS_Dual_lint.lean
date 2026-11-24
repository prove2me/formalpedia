-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_lint
-- name    : PositivityTheory.ThKEst.CS.Dual.lint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:38.237445+00:00
-- url     : https://prove2.me/theorems/4035af79-b41f-4813-a54f-730f01a767d0
-- title:
--   Dual: lint
-- statement:
--   The Dual construction uses the lint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L171-L174

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

theorem PositivityTheory.ThKEst.CS.Dual.lint (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) (f : G → ℝ≥0∞) :
    ∫⁻ u, f u ∂μ = ∑' ξ, ∫⁻ u in D, f (r ξ + u) ∂μ := by sorry
