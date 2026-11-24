-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_Dat_pow
-- name    : PositivityTheory.ThKEnd.Two.Dat.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:52.418398+00:00
-- url     : https://prove2.me/theorems/5fe531dd-4aad-434a-8954-69aa88d71140
-- title:
--   Dat: pow
-- statement:
--   The Dat construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ConvCont.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ConvCont.lean#L114-L117

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
omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [OpensMeasurableSpace X] [IsProbabilityMeasure lam]

theorem PositivityTheory.ThKEnd.Two.Dat.pow (h : Dat Γ n a lam l φ c) (k : ℕ) (g : G) : c (a * (a ^ k * g)) - c (a ^ k * g) = l ^ k * (c (a * g) - c g) := by sorry
