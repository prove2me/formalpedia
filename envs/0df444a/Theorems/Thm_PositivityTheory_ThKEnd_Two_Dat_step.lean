-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_Dat_step
-- name    : PositivityTheory.ThKEnd.Two.Dat.step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:17.245472+00:00
-- url     : https://prove2.me/theorems/d34c6998-7cda-4b42-8baa-9814a824f625
-- title:
--   Dat: step
-- statement:
--   The Dat construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ConvCont.lean#L140-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ConvCont.lean#L140-L181

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G} {a : G} {lam : Measure X}
  [IsProbabilityMeasure lam] {l : ℂ} {φ c : G → ℂ} {V : Set G} {η : G → ℝ} (μ : Measure G) [μ.IsHaarMeasure]

theorem PositivityTheory.ThKEnd.Two.Dat.step (hC : Cusp Γ n a) (hn : Continuous n) (h : Dat Γ n a lam l φ c) (hl : ‖l‖ < 1) {m : ℕ} (hm : Gr a (m + 1) φ)
    (hV : V ∈ 𝓝 (1 : G)) : ∃ η, Bump V η ∧ Gr a m (Two.conv μ η φ) := by sorry
