-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_bet_le
-- name    : PositivityTheory.ThKG.Loc.Bump.bet_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:01:26.750919+00:00
-- url     : https://prove2.me/theorems/b61f6c39-b012-4b1f-851e-519b8efc66b5
-- title:
--   Bump: bet le
-- statement:
--   The Bump construction uses the bet le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L26-L34

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

theorem PositivityTheory.ThKG.Loc.Bump.bet_le [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) : ∃ D : ℝ, ∀ k η, ‖bet ξ (k, η)‖ ≤ D * ‖η‖ := by sorry
