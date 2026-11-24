-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_rationalWeight_le
-- name    : PositivityTheory.ThKG.Loc.Bump.norm_rationalWeight_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:02.528362+00:00
-- url     : https://prove2.me/theorems/124fb482-a6bc-4698-b974-4c38b88e616f
-- title:
--   Bump: norm rational Weight le
-- statement:
--   The Bump construction uses the norm rational Weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L15-L22

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

theorem PositivityTheory.ThKG.Loc.Bump.norm_rationalWeight_le (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : ‖r0 κ e x‖ ≤ (1 + ‖x‖) ^ (2 * e * Fintype.card ι) := by sorry
