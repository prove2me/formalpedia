-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_FT_shift
-- name    : PositivityTheory.ThKG.Loc.Bump.FT_shift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:54.704804+00:00
-- url     : https://prove2.me/theorems/15ca10d9-10e5-4c24-a4ad-c08c27d86736
-- title:
--   Bump: FT shift
-- statement:
--   The Bump construction uses the FT shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/ContinuousOnRationalWeight.lean#L88-L91

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

theorem PositivityTheory.ThKG.Loc.Bump.FT_shift (g : (ι → ℂ) → ℂ) (b t : ι → ℂ) : ∫ x, ch (-pr x t) * g (x + b) = ch (pr b t) * FT g t := by sorry
