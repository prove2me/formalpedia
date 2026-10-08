-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_fderiv_chain_first_variational
-- name    : TeschlODE.Shared.flow_fderiv_chain_first_variational
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T15:45:43.16798+00:00
-- url     : https://prove2.me/theorems/fba77996-b1a9-4988-9aa0-04a3db91af8b
-- title:
--   The linearisation of the flow along a periodic orbit solves the first variational equation
-- statement:
--   **First variational equation (12.4)/(12.5).** Let `f ∈ C^k(M, ℝⁿ)` with `k ≥ 1`, `Φ` the flow of `ẋ = f(x)`, and `x₀ ∈ M` a periodic point of period `T > 0`. With `A t = fderiv ℝ f (Φ t x₀)` the linearisation (12.3), fix `t₀`. Then `J s = ∂Φ_(s - t₀)/∂x (Φ t₀ x₀)` satisfies
--
--   ```
--   HasDerivAt (fun s => ∂Φ_(s - t₀)/∂x (Φ t₀ x₀)) (A t * ∂Φ_(t - t₀)/∂x (Φ t₀ x₀)) t
--   ```
--
--   for every `t`, i.e. `∂ₜ J(t) = A(t) J(t)`.
--
--   **Proof (Teschl, p. 316).** Abbreviate `J(t, x) = ∂Φ_t/∂x (x)`. Then `J(0, x) = I` and, by interchanging the `t`- and `x`-derivatives, `J(t, x) = df_{Φ(t,x)} J(t, x)`. Substituting `x = Φ t₀ x₀` and shifting the time origin gives (2.48)/(2.49), which is the statement above.
--
--   **Where it sits.** Lemma 12.1 of the mission (`TeschlODE.PeriodicOrbits.principal_matrix_solution`) is exactly this record plus the initial condition `J(t₀, t₀) = I` plus Eq. (12.6). Splitting the three conjuncts into separate published children makes the reduction auditable: this record is the differential identity, `TeschlODE.Shared.flow_fderiv_sub_one_eq_id` is the initial condition, and `TeschlODE.Shared.flow_tangent_derivative_relation` is (12.6).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 316, §12.1 Eqs. (12.4)-(12.5); p. 46, §2.4 Eqs. (2.48)-(2.49)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- Teschl, §12.1, p. 316, Eq. (12.4): the first variational equation along a periodic orbit.

Let `f ∈ C^k(M, ℝⁿ)` with `k ≥ 1`, `Φ` the flow of `ẋ = f(x)` with maximal intervals `I`, and
`x₀ ∈ M` a periodic point of period `T > 0`. Put `A t = fderiv ℝ f (Φ t x₀)`, the linearisation
(12.3). For `t₀` fixed, the map `J : ℝ → ℝⁿ →ₗ[ℝ] ℝⁿ` given by `J s = ∂Φ_(s - t₀)/∂x (Φ t₀ x₀)`
satisfies the matrix initial value problem (12.4): `J t₀ = id` and `J' t = A t * J t`.

This is Eq. (12.5) read as "the principal matrix solution", i.e. the statement that the linearisation
of the flow is the fundamental matrix of `ẏ = A(t) y`. Teschl's proof abbreviates
`J(t, x) = ∂Φ_t/∂x (x)`, observes `J(0, x) = I`, and then interchanges the `t`- and `x`-derivatives
to get `J(t, x)' = df_{Φ(t,x)} J(t, x)`; with `x = Φ t₀ x₀` this is exactly (2.48)/(2.49)
specialised to the orbit. Uniqueness of the matrix IVP then identifies `J` with the principal
matrix solution `Π_{x₀}` of (12.4). -/
theorem flow_fderiv_chain_first_variational {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f M) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : 0 < T ∧ T ∈ I x₀ ∧ Φ T x₀ = x₀)
    (t₀ t : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (Φ (s - t₀)) (Φ t₀ x₀))
      ((fderiv ℝ f (Φ t x₀)).comp (fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀))) t := by sorry

end TeschlODE.Shared
