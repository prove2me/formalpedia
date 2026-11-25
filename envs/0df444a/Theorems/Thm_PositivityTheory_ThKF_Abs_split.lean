-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_Abs_split
-- name    : PositivityTheory.ThKF.Abs.split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:39.643678+00:00
-- url     : https://prove2.me/theorems/459b2eee-95e2-449a-81b7-7060d12139e0
-- title:
--   Abs: split
-- statement:
--   The Abs construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L61-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L61-L86

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Abs
open scoped InnerProductSpace
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem PositivityTheory.ThKF.Abs.split {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (W V : Submodule ℂ U) [FiniteDimensional ℂ V] (sV : ∀ k, ∀ y ∈ V, κ k y ∈ V) (u : U) (uV : u ∈ V) :
    ∃ y ∈ V, ∃ z ∈ V, y ∈ (ck (homs κ W))ᗮ ∧ z ∈ ck (homs κ W) ∧ u = y + z := by sorry
