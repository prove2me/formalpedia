-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_fderiv_smul_sub_one
-- name    : TeschlODE.Shared.flow_fderiv_smul_sub_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T15:44:24.078866+00:00
-- url     : https://prove2.me/theorems/fc8b8f13-38e3-4255-a292-fcd77d27fb04
-- title:
--   Along a periodic orbit the flow is differentiable in the initial condition at every time
-- statement:
--   **Flow differentiability at every time on a periodic orbit.** Let `f ∈ C^k(M, ℝⁿ)` with `k ≥ 1`, `M` open, `Φ` its flow with maximal intervals `I`, and `x₀ ∈ M` a periodic point of period `T > 0`. Then
--
--   1. `I x₀ = ℝ`;
--   2. for all `t₀, t : ℝ`, `y ↦ Φ (t - t₀) y` is differentiable at `Φ t₀ x₀`.
--
--   Clause 1 is formal: uniqueness of the maximal integral curve plus `Φ T x₀ = x₀` forces `I x₀ - T ⊆ I x₀`, and iterating from `T ∈ I x₀` gives `n T ∈ I x₀` for all `n ≥ 0`, which order-connectedness turns into `I x₀ = ℝ`. It is published separately as `TeschlODE.Shared.flow_periodic_implies_global_interval`; this record states it as a conjunct so that Chapter 12's time-quantified statements can be read off directly.
--
--   Clause 2 is the analytic content. Teschl's §2.4 proves that for `f ∈ C^k`, `k ≥ 1`, the flow is `C^k` jointly in `(t, x)` around every point of the integral cylinder, by differentiating the integral equation `x(t) = x₀ + ∫ f(s, x(s)) ds` and applying Gronwall to the difference quotient `θ(t, x) = (φ(t, x) − φ(t))/|x|`. In particular `∂Φ_t/∂x` exists at every point of the cylinder.
--
--   **Why this is the missing piece.** The mission's definition `TeschlODE_Shared_IsMaximalFlow` asserts only that `t ↦ Φ t x` is an integral curve on `I x` with `0 ∈ I x`, `Φ 0 x = x`, and that it is the unique such maximal curve. Every clause is about the time variable. Nothing constrains the dependence of `Φ` on `x`, so the Jacobian `∂Φ_t/∂x (x)` is not determined: perturbing `Φ` off the cylinder preserves every hypothesis while changing or destroying the derivative that Lemma 12.1 and Theorem 12.4 quantify over.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 46, §2.4 Eq. (2.48) and Theorem 2.10; p. 190, §6.2; p. 316, §12.1 Eq. (12.5)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- Teschl, §12.1, p. 316, Eq. (12.5), specialised to a periodic point.

Let `f ∈ C^k(M, ℝⁿ)` with `k ≥ 1` and `M` open, `Φ` its maximal flow, and let `x₀ ∈ M` be a
periodic point: `Φ T x₀ = x₀` for some `T > 0` with `T ∈ I x₀`. Then

* `I x₀ = ℝ` (a periodic point of a maximal unique flow is global);
* for every `t₀, t : ℝ`, the map `y ↦ Φ (t - t₀) y` is differentiable at `Φ t₀ x₀`; hence
  `fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀)` is a genuine continuous linear map of `ℝⁿ`.

This is the step that makes the whole of Chapter 12 well posed. The mission statements
`principal_matrix_solution` (Lemma 12.1) and `poincare_eigenvalues_monodromy` (Theorem 12.4) both
quantify over all `t₀, t : ℝ` and both read the Jacobian `fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀)` as a real
object, with the mission's own formalisation note insisting that "its existence is asserted as a
separate conjunct so no junk value can satisfy the statement". `IsMaximalFlow` constrains only the
*time* dependence of `Φ`, so without this bridge the Jacobian is not determined.

The source is §2.4, p. 46, Eq. (2.48) with Theorem 2.10, p. 46: for `f ∈ C^k`, `k ≥ 1`, the flow is
`C^k` in `(t, x)` near every point of the integral cylinder, so in particular
`∂Φ_t/∂x` exists there. -/
theorem flow_fderiv_smul_sub_one {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f M) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : 0 < T ∧ T ∈ I x₀ ∧ Φ T x₀ = x₀) :
    I x₀ = Set.univ ∧ ∀ t₀ t : ℝ, DifferentiableAt ℝ (Φ (t - t₀)) (Φ t₀ x₀) := by sorry

end TeschlODE.Shared
