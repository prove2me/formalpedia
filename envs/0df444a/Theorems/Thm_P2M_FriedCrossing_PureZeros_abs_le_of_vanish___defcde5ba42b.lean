-- Prove2me | Theorems.Thm_P2M_FriedCrossing_PureZeros_abs_le_of_vanish___defcde5ba42b
-- name    : P2M_FriedCrossing_PureZeros_abs_le_of_vanish___defcde5ba42b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:46:51.903975+00:00
-- url     : https://prove2.me/theorems/57afecd2-3b11-578d-9b3f-27dd3b6c735f
-- title:
--   P2 M Fried Crossing Pure Zeros abs le of vanish   defcde5ba42b: P2 M Fried Crossing Pure Zeros abs le of vanish   defcde5ba42b
-- statement:
--   g vanishes on the axis θ = 0 and has a bounded θ-derivative ⇒ |g(θ,τ)| ≤ K|θ|.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L143-L158
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L143-L158

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem P2M_FriedCrossing_PureZeros_abs_le_of_vanish___defcde5ba42b {g gθ : ℝ → ℝ → ℝ} {K ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ τ, g 0 τ = 0)
    (hθ : ∀ θ τ, HasDerivAt (fun θ => g θ τ) (gθ θ τ) θ)
    (hK : ∀ θ τ, |θ| < ε → |τ| < ε → |gθ θ τ| ≤ K)
    {θ τ : ℝ} (hθε : |θ| < ε) (hτε : |τ| < ε) : |g θ τ| ≤ K * |θ| := by sorry

alias «FriedCrossing».«PureZeros».«abs_le_of_vanish_θ» := P2M_FriedCrossing_PureZeros_abs_le_of_vanish___defcde5ba42b
