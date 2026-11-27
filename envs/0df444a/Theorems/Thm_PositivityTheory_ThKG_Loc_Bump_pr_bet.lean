-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_pr_bet
-- name    : PositivityTheory.ThKG.Loc.Bump.pr_bet
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:20.225852+00:00
-- url     : https://prove2.me/theorems/3847cad9-d85c-510e-a118-8afa9749062d
-- title:
--   Bump: pr bet
-- statement:
--   The Bump construction uses the pr bet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L19-L22

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
omit [TopologicalSpace K]

theorem PositivityTheory.ThKG.Loc.Bump.pr_bet (ξ : K → ι → n → ℂ) (k : K) (η : XS (ι × n)) (t : ι → ℂ) : pr (bet ξ (k, η)) t = ⟪η, pim ξ (k, t)⟫ := by sorry
