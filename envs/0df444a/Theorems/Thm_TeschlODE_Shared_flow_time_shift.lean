-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_time_shift
-- name    : TeschlODE.Shared.flow_time_shift
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-04T15:43:51.290992+00:00
-- url     : https://prove2.me/theorems/eab19757-86fd-445e-ac1a-506b74a8a595
-- title:
--   The flow is time-translation invariant: Φ(s + T) y = Φ s (Φ T y) and Φ(s - s) y = y
-- statement:
--   **Time-homogeneity at zero shift.** For every `y ∈ M` and every `s : ℝ`, the flow satisfies `Φ (s - s) y = y`, i.e. `Φ 0 y = y`.
--
--   This is one of the two clauses of `TeschlODE_Shared_IsMaximalFlow` itself (`Φ 0 x = x` for `x ∈ M`), which the platform records as the normalising condition (6.12) alongside the flow property (6.11). It is recorded separately here because Lemma 12.1 needs it in a form that is directly applicable: the target's first conjunct is
--
--   ```
--   ∀ t₀ : ℝ, fderiv ℝ (Φ (t₀ - t₀)) (Φ t₀ x₀) = ContinuousLinearMap.id ℝ (Fin n → ℝ)
--   ```
--
--   whose *left-hand side* is the Jacobian of `Φ (t₀ - t₀) = Φ 0`, a constant map in the variable `y`; its derivative is therefore the identity at every point, once one knows the map is the constant `y ↦ Φ 0 y = y`. The substantive content of that conjunct is the separate fact that the flow's Jacobian at zero time-shift is the identity, which is the other bridge child; this record supplies the easy but necessary normalisation step.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 190, §6.2, Eq. (6.12)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- Teschl, §6.2, p. 190, Eq. (6.11), read off the uniqueness clause of `IsMaximalFlow`:

* `Φ (s + T) y = Φ s (Φ T y)` for every `y ∈ M` with `T ∈ I y` and `s ∈ I (Φ T y)`
  (the flow property (6.11), together with the fact that both sides are integral curves through
  `Φ T y` at time `0`); and
* `Φ (s - s) y = y` for every `y ∈ M`, i.e. the flow fixes the origin of time (6.12).

Together these give `Φ (s - s) y = y`, so the Jacobian at zero time-shift is evaluated at `y`
itself. -/
theorem flow_time_shift {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ))
    (hM : IsOpen M) (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (y : Fin n → ℝ) (s : ℝ) :
    Φ (s - s) y = y := by sorry

end TeschlODE.Shared
