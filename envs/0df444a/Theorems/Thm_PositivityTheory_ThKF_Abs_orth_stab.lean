-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_Abs_orth_stab
-- name    : PositivityTheory.ThKF.Abs.orth_stab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:51.996617+00:00
-- url     : https://prove2.me/theorems/ccc9e7ad-ca6a-4a5d-bde3-d9de1753b0a2
-- title:
--   Abs: orth stab
-- statement:
--   The Abs construction uses the orth stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L11-L17

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

theorem PositivityTheory.ThKF.Abs.orth_stab {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Y : Submodule ℂ U) (hY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y) (k : K) (z : U) (hz : z ∈ Yᗮ) : κ k z ∈ Yᗮ := by sorry
