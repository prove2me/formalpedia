-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_periodic_orbit_global_everywhere
-- name    : TeschlODE.Shared.flow_periodic_orbit_global_everywhere
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-04T15:58:10.704978+00:00
-- url     : https://prove2.me/theorems/ef75301d-4442-4412-9c72-11f0eb5b723c
-- title:
--   Every point of a periodic orbit of a maximal unique flow has global interval of existence
-- statement:
--   **Every point of a periodic orbit is global.** Let `f : ℝⁿ → ℝⁿ`, `M ⊆ ℝⁿ` open, `Φ` the flow of `ẋ = f(x)` with maximal intervals `I`. If `x₀ ∈ M` and `Φ T x₀ = x₀` for some `T > 0` with `T ∈ I x₀`, then `I z = ℝ` for **every** `z ∈ M`, not merely for `x₀`.
--
--   **Proof.** First `I x₀ = ℝ`: the translate `ψ s := Φ (s + T) x₀` is an integral curve of the same field on `J := I x₀ - T` (chain rule through `s ↦ s + T`), with `0 ∈ J` and `ψ 0 = Φ T x₀ = x₀`. The uniqueness clause of `IsMaximalFlow` gives `J ⊆ I x₀`, i.e. `s ∈ I x₀ → s - T ∈ I x₀`. Since `I x₀` is open and order-connected and contains `0` and `T`, iterating the shift-down yields `n T ∈ I x₀` for all `n ≥ 0`, hence `[0, ∞) ⊆ I x₀`, and shifting down again gives `(-∞, 0] ⊆ I x₀`.
--
--   Now fix `t₀` with `z := Φ t₀ x₀`. Since `I x₀ = ℝ` we get `t₀ ∈ I x₀`, so the range clause of `IsIntegralCurve` gives `z ∈ M`. The curve `r ↦ Φ (r + t₀) x₀` is an integral curve of the same field on `{r | r + t₀ ∈ I x₀} = ℝ` (chain rule through `r ↦ r + t₀`), it contains `0`, and at `0` it takes the value `z`. The uniqueness clause of `IsMaximalFlow` applied at `z` therefore gives `ℝ ⊆ I z`. ∎
--
--   **No analytic input.** Every step uses only the clauses of `IsMaximalFlow`, the facts that `I z` is open and order-connected, and elementary reindexing. In particular this is *not* Picard–Lindelöf global existence, which would require a growth bound on `f`; periodicity supplies a substitute here.
--
--   **Why Chapter 12 needs it.** `TeschlODE.PeriodicOrbits.principal_matrix_solution` concludes `∀ t₀ t : ℝ, DifferentiableAt ℝ (Φ (t - t₀)) (Φ t₀ x₀) ∧ …`, and `TeschlODE.PeriodicOrbits.poincare_eigenvalues_monodromy` concludes `∀ t₀ : ℝ, LinearMap.charpoly (fderiv ℝ (Φ T) (Φ t₀ x₀) : …) = (Polynomial.X - 1) * L.charpoly`. Both read the Jacobian at `Φ t₀ x₀` for **every** real time. The mission's formalisation note for Lemma 12.1 says outright that the derivative's "existence is asserted as a separate conjunct so no junk value can satisfy the statement" - which is possible only once the orbit is known to be global, so that `Φ (t - t₀) x₀` and `Φ t₀ x₀` both lie in the region where the flow is a genuine solution.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2 Eqs. (6.8)-(6.9); p. 192, §6.3

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- Teschl, §6.3, p. 192, together with §6.2, p. 189, Eqs. (6.8)-(6.9): every point of a
periodic orbit of a maximal unique flow has global interval of existence.

If `x₀ ∈ M` is a periodic point of the flow `Φ` with maximal intervals `I`, so that
`Φ T x₀ = x₀` for some `T > 0` with `T ∈ I x₀`, then not only `I x₀ = ℝ` but in fact

`∀ z ∈ M, I z = ℝ`.

Indeed `I x₀ = ℝ` (see `TeschlODE.Shared.flow_periodic_implies_global_interval`), so every
`Φ t x₀` lies in `M` by the range clause of `IsIntegralCurve`, and the curve
`r ↦ Φ (r + t₀) x₀` is an integral curve of the same field on all of `ℝ` with value `x₀` at time
`0`; the uniqueness clause of `IsMaximalFlow` applied at `z = Φ t₀ x₀` therefore gives
`ℝ ⊆ I (Φ t₀ x₀)`. This is purely formal and uses no analytic input.

This is what makes the Chapter 12 statements well posed. `principal_matrix_solution` (Lemma 12.1)
and `poincare_eigenvalues_monodromy` (Theorem 12.4) both quantify over **all** `t₀, t : ℝ` and
read the Jacobian `fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀)` as a real object. For a merely local flow
that Jacobian is unconstrained - and, off `M`, not even a derivative of anything - so the
statements would be ill posed. Periodicity is exactly what removes the problem. -/
theorem flow_periodic_orbit_global_everywhere {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ)
    (hT0 : 0 < T) (hTI : T ∈ I x₀) (hper : Φ T x₀ = x₀) :
    ∀ z ∈ M, I z = Set.univ := by sorry

end TeschlODE.Shared
