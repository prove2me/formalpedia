-- Prove2me | Theorems.Thm_PHarmClassicalGradient
-- name    : PHarmClassicalGradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:35.787809+00:00
-- url     : https://prove2.me/theorems/d8997fa4-cf31-4363-92d2-5470c676a9dc
-- title:
--   PHarm Classical Gradient: PHarm Classical Gradient
-- statement:
--   The classical gradient of a limit object, read off from the approximating
--   gradients.  If each `u n` has classical gradient `g n` at every point of an open
--   `Ω`, the `g n` converge to `G` uniformly on every compact subset of `Ω`, and
--   `u n → U` pointwise on `Ω`, then `U` has classical gradient `G x` at every `x ∈ Ω`;
--   in particular `gradient U = G` on `Ω`.
--
--   This is the bridge that lets a hypothesis about a CLASSICAL gradient — such as
--   `Du x₀ = 0` at a critical point — be read off a gradient produced by a limit.  Note
--   it needs no measure theory and no a.e. uniqueness of weak gradients: uniform
--   convergence of the derivatives identifies the limit derivative outright.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmClassicalGradient.lean#L13-L42
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmClassicalGradient.lean#L13-L42

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_PHarmClassicalGradient
set_option autoImplicit false

theorem PHarmClassicalGradient (Ω : Set Plane) (hΩ : IsOpen Ω)
    (u : ℕ → Plane → ℝ) (g : ℕ → Plane → Plane) (U : Plane → ℝ) (G : Plane → Plane)
    (hderiv : ∀ n : ℕ, ∀ x ∈ Ω, HasGradientAt (u n) (g n x) x)
    (hconv : ∀ K : Set Plane, K ⊆ Ω → IsCompact K → TendstoUniformlyOn g G Filter.atTop K)
    (hptwise : ∀ x ∈ Ω, Filter.Tendsto (fun n => u n x) Filter.atTop (nhds (U x))) :
    ∀ x ∈ Ω, HasGradientAt U (G x) x ∧ gradient U x = G x := by sorry
