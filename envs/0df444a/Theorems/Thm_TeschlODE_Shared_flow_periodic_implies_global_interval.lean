-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_periodic_implies_global_interval
-- name    : TeschlODE.Shared.flow_periodic_implies_global_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T15:43:39.658741+00:00
-- url     : https://prove2.me/theorems/86e07d27-76d2-460f-a31c-6ab1d115c7e6
-- title:
--   A periodic point of a maximal unique flow has global interval of existence
-- statement:
--   **A periodic point of a maximal unique flow exists for all time.** Let `f : ℝⁿ → ℝⁿ`, `M ⊆ ℝⁿ` open, and `Φ` the flow of `ẋ = f(x)` with maximal intervals `I x`. If `x ∈ M` and `Φ T x = x` for some `T > 0` lying in `I x`, then `I x = ℝ`.
--
--   The flow is only assumed to be *local*: `TeschlODE_Shared_IsMaximalFlow` asserts that `t ↦ Φ t x` is an integral curve on the open order-connected interval `I x` with `0 ∈ I x` and `Φ 0 x = x`, and that it is the unique such maximal integral curve through `x`. No hypothesis says `I x = ℝ`; the platform's own formalisation note says so explicitly: "The flow is local: nothing asserts `I x = ℝ`."
--
--   **Why the Chapter 12 statements need this.** `TeschlODE.PeriodicOrbits.principal_matrix_solution` concludes
--
--   ```
--   ∀ t₀ t : ℝ, DifferentiableAt ℝ (Φ (t - t₀)) (Φ t₀ x₀) ∧ … ∧ f (Φ t x₀) = fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀) (…)
--   ```
--
--   and `TeschlODE.PeriodicOrbits.poincare_eigenvalues_monodromy` concludes
--
--   ```
--   ∀ t₀ : ℝ, LinearMap.charpoly (fderiv ℝ (Φ T) (Φ t₀ x₀) : …) = (Polynomial.X - 1) * L.charpoly
--   ```
--
--   Both quantify over **every** real time. For a merely local flow `Φ (t - t₀) x₀` and `Φ t₀ x₀` are unconstrained when the time leaves `I x₀`, so `fderiv` there would be a junk value. The mission's formalisation notes make this an explicit design decision — in `principal_matrix_solution`, "its existence is asserted as a separate conjunct so no junk value can satisfy the statement" — which is precisely an admission that the derivative is only real where the flow is defined.
--
--   Periodicity is what repairs this. If `Φ T x = x` with `T ∈ I x` and `T > 0`, then the translate `ψ(s) := Φ (s + T) x` is an integral curve of the same field on `J := I x - T`, with `ψ 0 = Φ T x = x` and `0 ∈ J`. The uniqueness clause of `IsMaximalFlow` therefore gives
--
--   * `J ⊆ I x`, i.e. `s ∈ I x → s - T ∈ I x`, and
--   * `∀ t ∈ J, Φ (t + T) x = Φ t x`.
--
--   Iterating the first bullet from `T ∈ I x` yields `n T ∈ I x` for every `n ≥ 0`. Since `I x` is open and order-connected and contains `0`, containing all `n T` forces the whole ray `[0, ∞) ⊆ I x`; applying `s ↦ s - T` repeatedly gives `(-∞, 0] ⊆ I x` as well. Hence `I x = ℝ`.
--
--   This is a settled, purely formal consequence of the two clauses of `IsMaximalFlow` plus one periodicity hypothesis. It uses no analytic input at all — in particular it is *not* the Picard–Lindelöf global-existence theorem, which would need a growth bound on `f`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2 and p. 192, §6.3

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- Teschl, §6.3, p. 192, combined with §6.2, p. 189, Eqs. (6.8)–(6.9). If `x ∈ M` is a
periodic point of the flow `Φ` with maximal intervals `I`, in the sense that `Φ T x = x` for
some `T > 0` with `T ∈ I x`, then in fact `I x = ℝ`.

The book states this as "it is not hard to see" in the orbit discussion: a solution that returns
to its starting point repeats forever, and uniqueness of the maximal integral curve propagates
that periodicity to the whole maximal interval. Formally the argument is: the translate
`ψ(s) = Φ (s + T) x` is again an integral curve of the same field through `x` at time `0`, so the
uniqueness clause of `IsMaximalFlow` forces `Φ (s + T) x = Φ s x` on `I x - T` and forces
`I x - T ⊆ I x`; iterating from `T ∈ I x` gives `n T ∈ I x` for all `n ≥ 0`, and order-connectedness
then fills all of `ℝ`.

This is needed because the Chapter 12 statements quantify over **all** times `t₀, t : ℝ`. For
a merely local flow, `Φ (t - t₀) x₀` is meaningless when `t - t₀ ∉ I x₀`, so those statements
would be ill-posed; periodicity is exactly what makes them well posed. -/
theorem flow_periodic_implies_global_interval {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (x : Fin n → ℝ) (hx : x ∈ M) (T : ℝ)
    (hT0 : 0 < T) (hTI : T ∈ I x) (hper : Φ T x = x) :
    I x = Set.univ := by sorry

end TeschlODE.Shared
