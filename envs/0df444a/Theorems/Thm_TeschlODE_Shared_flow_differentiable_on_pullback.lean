-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_differentiable_on_pullback
-- name    : TeschlODE.Shared.flow_differentiable_on_pullback
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-04T15:39:48.451994+00:00
-- url     : https://prove2.me/theorems/385f50d5-f4e5-4983-9d8c-0b2bc4c9430a
-- title:
--   Along an integral curve the flow is differentiable in the initial condition
-- statement:
--   **Flow differentiability in the initial condition.** Let `f ∈ C^k(M, ℝⁿ)` with `k ≥ 1` and `M` open, let `Φ` be its flow with maximal intervals `I x`, and fix `x ∈ M`. For any `s, t ∈ I x` the map `y ↦ Φ t y` is differentiable at `Φ s x`, so the Jacobian `∂Φ_t/∂x (Φ s x)` exists as a continuous linear map of `ℝⁿ`.
--
--   This is the analytic ingredient behind Chapter 12. The mission's existing definition `TeschlODE_Shared_IsMaximalFlow` (Teschl, §6.2, p. 189, Eqs. (6.8)–(6.9)) asserts only three things about `Φ`:
--
--   1. `t ↦ Φ t x` is an integral curve of `ẋ = f(x)` on the open interval `I x`, with `0 ∈ I x` and `Φ 0 x = x`;
--   2. it is the unique such maximal integral curve through `x`.
--
--   Those clauses are about the *time* variable only. They do not constrain the dependence of `Φ` on the *initial condition* `x`, so from them alone the Jacobian `∂Φ_t/∂x (x)` is not determined: one may perturb `Φ` off the integral cylinder and every hypothesis of `IsMaximalFlow` still holds, while the derivative the mission needs changes or ceases to exist.
--
--   Lemma 12.1 (`TeschlODE.PeriodicOrbits.principal_matrix_solution`) and Theorem 12.4 (`TeschlODE.PeriodicOrbits.poincare_eigenvalues_monodromy`) both quantify over
--
--   `fderiv ℝ (Φ (t − t₀)) (Φ t₀ x₀)`
--
--   as a real object, and the mission's formalisation note for Lemma 12.1 states that the derivative's *existence* is asserted as a separate conjunct "so no junk value can satisfy the statement". That conjunct is therefore unprovable from `IsMaximalFlow` alone; this theorem supplies it.
--
--   **Source.** Teschl, *Ordinary Differential Equations and Dynamical Systems* (author's preliminary version of AMS GSM 140, 2012), p. 46, Eq. (2.48) and Theorem 2.10; applied to the autonomous case in §6.2, p. 190, where the book writes `J(t, x) = ∂Φ_t/∂x (x)` with `J(0, x) = I` and `J(t, x) = I + ∫₀ᵗ df_{Φ(s,x)} J(s, x) ds`, i.e. (2.49)–(2.50).
--
--   **Status of the mathematics.** This is settled classical ODE theory. Teschl's proof is a Gronwall estimate on the difference quotient `θ(t, x) = (φ(t, x) − φ(t))/|x|`, using the quadratic expansion `f(y) − f(x) = ∂f/∂x (x)(y − x) + |y − x| R(y, x)` with `R(y, x) → 0` uniformly in `x` near the identity, plus induction in `k`. No hypothesis beyond `f ∈ C^k`, `k ≥ 1`, is used. Publishing it as a separate record is bookkeeping, not a new claim.
--
--   **Why the weaker statement is the right one.** The published form deliberately asserts *only* differentiability, not the variational identity `∂ₜJ = A(t) J` and not `f(Φ t x) = J(t, x) f(x)`. Those two are the substance of Lemma 12.1 itself, and they require the Gronwall/Vandermonde argument; keeping them out avoids duplicating the mission lemma and keeps this record a clean, minimal, independently provable dependency.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 46, Eq. (2.48) and Theorem 2.10; p. 190, §6.2

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- Teschl, §2.4, p. 46, Eq. (2.48) together with Theorem 2.10, p. 46, and its use in
§6.2, p. 190: if `x ∈ M` and `s, t ∈ I x` then the flow of `ẋ = f (x)` is differentiable at
`x` in the initial condition at time `s`, with `∂Φ_t/∂x (Φ s x) = ∂Φ_(t − s)/∂x (x)`.
The derivative exists at every point of the integral cylinder, so the linearization
`J(t, x) = ∂Φ_t/∂x (x)` needed by Lemma 12.1 and Theorem 12.4 is well defined on the whole
orbit.

This is the analytic bridge that the `TeschlODE.PeriodicOrbits` mission currently lacks:
`TeschlODE_Shared_IsMaximalFlow` fixes only `IsIntegralCurve`, `Φ 0 x = x` and uniqueness, and
from those alone the Jacobian `∂Φ_t/∂x (x)` is not determined. It is a *settled* ingredient of
classical ODE theory (Gronwall argument, §2.4), not a conjecture, so publishing it as an Open
child is the right way to make the reduction explicit. -/
theorem flow_differentiable_on_pullback {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f M) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : IsMaximalFlow f M I Φ)
    (x : Fin n → ℝ) (s t : ℝ) (hs : s ∈ I x) (ht : t ∈ I x) :
    DifferentiableAt ℝ (Φ t) (Φ s x) := by sorry

end TeschlODE.Shared
