-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_pr_add
-- name    : PositivityTheory.ThKG.Loc.Bump.pr_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:04:44.989496+00:00
-- url     : https://prove2.me/theorems/81a6f2c3-0e75-5af6-954a-192dd0d91453
-- title:
--   Bump: pr add
-- statement:
--   The Bump construction uses the pr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L85-L86

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

theorem PositivityTheory.ThKG.Loc.Bump.pr_add (x y t : ι → ℂ) : pr (x + y) t = pr x t + pr y t := by sorry
