-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_rationalWeight_succ_mul_inv_norm
-- name    : PositivityTheory.ThKG.Loc.Bump.rationalWeight_succ_mul_inv_norm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:47.26558+00:00
-- url     : https://prove2.me/theorems/7684b221-52a3-4154-8987-f17afb907f9a
-- title:
--   Bump: rational Weight succ mul inv norm
-- statement:
--   The Bump construction uses the rational Weight succ mul inv norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L97-L103

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

theorem PositivityTheory.ThKG.Loc.Bump.rationalWeight_succ_mul_inv_norm (κ : ι → ℕ) (e : ℕ) {x : ι → ℂ} (hx : ∀ w, x w ≠ 0) :
    r0 κ (e + 1) x * ((∏ w, ‖x w‖ ^ 2 : ℝ) : ℂ)⁻¹ = r0 κ e x := by sorry
