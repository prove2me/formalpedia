-- Prove2me | Theorems.Thm_TaylorRemainder
-- name    : TaylorRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:10.202971+00:00
-- url     : https://prove2.me/theorems/1e9aa290-1f31-45e0-9742-df21278ad274
-- title:
--   Taylor Remainder: Taylor Remainder
-- statement:
--   Taylor's theorem with Lagrange remainder, in the DIAGONAL form this development uses and
--   with a general (not necessarily vanishing) degree-`k` Taylor polynomial: if `u` is `C^(k+1)` on
--   `ball x₀ ρ` with `‖D^(k+1) u‖ ≤ M` there, then
--
--   `|u x - TaylorPoly k u x₀ x| ≤ M / (k+1)! * ‖x - x₀‖^(k+1)`     for every `x ∈ ball x₀ ρ`.
--
--   Nothing in the tablet supplies this.  `TaylorVanishingDecay` assumes every diagonal Taylor
--   coefficient vanishes, so it says nothing when the polynomial is nonzero, and
--   `PolyInverseEstimate` runs the other way, bounding a polynomial's derivatives by its sup norm.
--   The paper needs the present bound where it turns `Noncritical`'s `C^(k+1)(B_tau)` estimate into
--   `‖v_L - Q‖_{L^∞(B_t)} ≤ C_delta t^(k+1)` (paper line 253).
--
--   The proof restricts to the ray `s ↦ u (x₀ + s • (x - x₀))` and applies the one-variable
--   Taylor-Lagrange theorem on `[0,1]`, which is why the only multivariate input is the ray
--   transfer of `IteratedDerivAlongRay`; no multivariate Taylor development and no symmetry of the
--   derivative tensor is used.  The hypotheses `0 < ρ` and `0 ≤ M` are the natural domain
--   conditions and are not needed by the argument.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorRemainder.lean#L22-L117
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorRemainder.lean#L22-L117

import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_TaylorRemainder
import Theorems.Thm_IteratedDerivAlongRay

set_option autoImplicit false
set_option linter.unusedVariables false

theorem TaylorRemainder (u : Plane → ℝ) (x₀ : Plane) (ρ : ℝ) (hρ : 0 < ρ)
    (k : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) u (Metric.ball x₀ ρ))
    (hbd : ∀ x ∈ Metric.ball x₀ ρ, ‖iteratedFDeriv ℝ (k + 1) u x‖ ≤ M) :
    ∀ x ∈ Metric.ball x₀ ρ,
      |u x - TaylorPoly k u x₀ x| ≤ M / (Nat.factorial (k + 1) : ℝ) * ‖x - x₀‖ ^ (k + 1) := by sorry
