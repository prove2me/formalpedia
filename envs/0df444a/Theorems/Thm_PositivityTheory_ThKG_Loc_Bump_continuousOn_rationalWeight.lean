-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuousOn_rationalWeight
-- name    : PositivityTheory.ThKG.Loc.Bump.continuousOn_rationalWeight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:34.882294+00:00
-- url     : https://prove2.me/theorems/44aa1d4d-79a5-402c-8158-8d9dbaf02af7
-- title:
--   Bump: continuous On rational Weight
-- statement:
--   The Bump construction uses the continuous On rational Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L47-L50

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

theorem PositivityTheory.ThKG.Loc.Bump.continuousOn_rationalWeight (κ : ι → ℕ) (e : ℕ) : ContinuousOn (r0 κ e) {x | ∀ w, x w ≠ 0} := by sorry
