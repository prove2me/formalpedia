-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_Dec_bound
-- name    : PositivityTheory.ThKG.Loc.Bump.Dec.bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:32.592821+00:00
-- url     : https://prove2.me/theorems/d4587659-bac3-43f9-8179-001c7918fff7
-- title:
--   Dec: bound
-- statement:
--   The Dec construction uses the bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L34-L45

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace
variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {K : Type} [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem PositivityTheory.ThKG.Loc.Bump.Dec.bound {a : K × (ι → ℂ) → ℂ} (ha : Dec a) (M : ℕ) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ k x b : _,
    ‖a (k, x + b)‖ * (1 + ‖x‖) ^ M ≤ C * (1 + ‖b‖) ^ N * mj x := by sorry
