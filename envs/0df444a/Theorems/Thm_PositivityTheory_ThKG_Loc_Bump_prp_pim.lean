-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_prp_pim
-- name    : PositivityTheory.ThKG.Loc.Bump.prp_pim
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:00.203085+00:00
-- url     : https://prove2.me/theorems/febcb260-96d1-4355-ba19-994fd9b18378
-- title:
--   Bump: prp pim
-- statement:
--   The Bump construction uses the prp pim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L44-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L44-L70

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

theorem PositivityTheory.ThKG.Loc.Bump.prp_pim [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) (hne : ∀ k w, ξ k w ≠ 0) (k₁ : K) :
    Prp (pim ξ) (pim ξ (k₁, 1)) := by sorry
