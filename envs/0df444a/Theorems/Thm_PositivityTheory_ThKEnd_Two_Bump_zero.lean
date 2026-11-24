-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_Bump_zero
-- name    : PositivityTheory.ThKEnd.Two.Bump.zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:41.525618+00:00
-- url     : https://prove2.me/theorems/56ef843a-ec62-45f9-a428-460d101bc36d
-- title:
--   Bump: zero
-- statement:
--   The Bump construction uses the zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ConvCont.lean#L53-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ConvCont.lean#L53-L72

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

theorem PositivityTheory.ThKEnd.Two.Bump.zero (D : G → ℂ) (hD : Continuous D) (g : G) (h : ∀ V ∈ 𝓝 (1 : G), ∃ η, Bump V η ∧ conv μ η D g = 0) : D g = 0 := by sorry
