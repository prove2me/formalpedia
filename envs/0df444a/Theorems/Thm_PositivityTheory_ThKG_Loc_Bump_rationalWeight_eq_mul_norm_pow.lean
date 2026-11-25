-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_rationalWeight_eq_mul_norm_pow
-- name    : PositivityTheory.ThKG.Loc.Bump.rationalWeight_eq_mul_norm_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:09.708192+00:00
-- url     : https://prove2.me/theorems/8b9d45c2-64da-4142-8a70-5ac008d8903d
-- title:
--   Bump: rational Weight eq mul norm pow
-- statement:
--   The Bump construction uses the rational Weight eq mul norm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L105-L109

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm
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
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate
variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]

theorem PositivityTheory.ThKG.Loc.Bump.rationalWeight_eq_mul_norm_pow (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : r0 κ e x = r0 κ 0 x * ((nm x : ℝ) : ℂ) ^ e := by sorry
