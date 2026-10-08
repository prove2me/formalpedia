-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_fderiv_sub_one_eq_id
-- name    : TeschlODE.Shared.flow_fderiv_sub_one_eq_id
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T15:44:12.521715+00:00
-- url     : https://prove2.me/theorems/da054d78-4e25-436f-be0a-7e7bfb3bf4fe
-- title:
--   The Jacobian of the flow at zero time-shift is the identity
-- statement:
--   **The flow's Jacobian at zero time-shift is the identity.** Let `Φ` be the flow of `ẋ = f(x)` on `M` and let `x ∈ M`. For any `s, t ∈ I x`,
--
--   `fderiv ℝ (Φ (s - s)) x = ContinuousLinearMap.id ℝ (Fin n → ℝ)`
--
--   Since `s - s = 0` and (6.12) gives `Φ 0 y = y`, the map whose derivative is taken is the constant identity map `y ↦ y`, and the Fréchet derivative of a constant map at every point is the identity linear map. No analytic content is involved.
--
--   This is the first clause of Lemma 12.1 (12.5), `J(t₀, t₀) = I`, with `J(t, t₀) = ∂Φ_{t - t₀}/∂x (Φ t₀ x₀)`. At `t = t₀` the shift vanishes, so the Jacobian collapses to the identity Jacobian evaluated at the initial point itself. The platform's Lemma 12.1 states it as
--
--   `∀ t₀ : ℝ, fderiv ℝ (Φ (t₀ - t₀)) (Φ t₀ x₀) = ContinuousLinearMap.id ℝ (Fin n → ℝ)`
--
--   i.e. at the base point `Φ t₀ x₀` rather than at `x₀`; applying the statement at `x := Φ t₀ x₀` requires `Φ t₀ x₀ ∈ M` and `t₀ ∈ I (Φ t₀ x₀)`, which follow from the integral-curve clause of `IsMaximalFlow` once the interval is known to be global (see `TeschlODE.Shared.flow_periodic_implies_global_interval`).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 190, §6.2, and p. 316, §12.1 Eq. (12.5)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- Teschl, §6.2, p. 190: abbreviating `J(t, x) = ∂Φ_t/∂x (x)`, one has `J(0, x) = I`.

The book's proof uses Problem 1.8, that the autonomous flow satisfies `Φ(t, x) = Φ(t, 0, x)`,
so `J(t, 0) = ∂/∂x Φ_t(0) = ∂/∂y (y ↦ y)` at the identity initial condition, which is the
identity linear map. Formally: if `x ∈ M` and `s, t ∈ I x` then
`fderiv ℝ (Φ (s - s)) x = ContinuousLinearMap.id ℝ (Fin n → ℝ)`, because the composite
`Φ (s - s) = Φ 0` is the constant map `y ↦ y` (6.12) and the Fréchet derivative of a constant
map at every point is the identity. -/
theorem flow_fderiv_sub_one_eq_id {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f M) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : IsMaximalFlow f M I Φ)
    (x : Fin n → ℝ) (s t : ℝ) (hx : x ∈ M) (hs : s ∈ I x) (ht : t ∈ I x) :
    fderiv ℝ (Φ (s - s)) x = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by sorry

end TeschlODE.Shared
