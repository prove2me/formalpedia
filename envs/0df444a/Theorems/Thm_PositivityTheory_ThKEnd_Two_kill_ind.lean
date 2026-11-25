-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_kill_ind
-- name    : PositivityTheory.ThKEnd.Two.kill_ind
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:47.346793+00:00
-- url     : https://prove2.me/theorems/89f73d38-024b-49c6-b286-656b290d953f
-- title:
--   Two: kill ind
-- statement:
--   The Two construction uses the kill ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ConvCont.lean#L183-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ConvCont.lean#L183-L199

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

theorem PositivityTheory.ThKEnd.Two.kill_ind (hC : Cusp Γ n a) (hn : Continuous n) (hl : ‖l‖ < 1) (P : (G → ℂ) → (G → ℂ) → Prop)
    (h0 : ∀ φ c, Dat Γ n a lam l φ c → (∃ M, ∀ g, ‖φ g‖ ≤ M) → P φ c)
    (h1 : ∀ φ c, Dat Γ n a lam l φ c → (∀ V ∈ 𝓝 (1 : G), ∃ η, Bump V η ∧ P (conv μ η φ) (conv μ η c)) → P φ c)
    (m : ℕ) : ∀ φ c, Dat Γ n a lam l φ c → Gr a m φ → P φ c := by sorry
