-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_exists_FT_ne
-- name    : PositivityTheory.ThKG.Loc.Bump.exists_FT_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:44.544936+00:00
-- url     : https://prove2.me/theorems/4df9b6a9-bc48-4d74-bd71-236265ca6b91
-- title:
--   Bump: exists FT ne
-- statement:
--   The Bump construction uses the exists FT ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L72-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L72-L95

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

theorem PositivityTheory.ThKG.Loc.Bump.exists_FT_ne {a : (ι → ℂ) → ℂ} (ha : Continuous a) (hi : Integrable a) (h0 : a 0 ≠ 0) : ∃ t, FT a t ≠ 0 := by sorry
