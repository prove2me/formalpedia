-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_Abs_proj_equiv
-- name    : PositivityTheory.ThKF.Abs.proj_equiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:00.301804+00:00
-- url     : https://prove2.me/theorems/136f75fe-f810-4ca3-9206-b7f87ce6d86b
-- title:
--   Abs: proj equiv
-- statement:
--   The Abs construction uses the proj equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L19-L24

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

theorem PositivityTheory.ThKF.Abs.proj_equiv {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Y : Submodule ℂ U) [FiniteDimensional ℂ Y] (hY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y) (k : K) (x : U) :
    Y.starProjection (κ k x) = κ k (Y.starProjection x) := by sorry
