-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_comp_add_isIntegralCurve
-- name    : TeschlODE.Shared.flow_comp_add_isIntegralCurve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T18:53:21.036241+00:00
-- url     : https://prove2.me/theorems/86475078-d80f-4266-973a-9982097d6476
-- title:
--   The time-translate of the flow along an integral curve is an integral curve
-- statement:
--   **Flow range and translates.** Let `f : ℝⁿ → ℝⁿ`, `M ⊆ ℝⁿ` open, and `Φ` the flow of `ẋ = f(x)` with maximal intervals `I`. For `x ∈ M` and `t ∈ I x` the point `Φ t x` lies in `M`, and the translate `s ↦ Φ (s + c) x` is an integral curve of the same field on `{s | s + c ∈ I x}`.
--
--   **Why it needs its own record.** `IsIntegralCurve` is a four-way conjunction
--
--   ```lean
--   IsOpen J ∧ J.OrdConnected ∧ (∀ t ∈ J, φ t ∈ M) ∧ ∀ t ∈ J, HasDerivAt φ (f (φ t)) t
--   ```
--
--   and `IsMaximalFlow` wraps it as
--
--   ```lean
--   ∀ x ∈ M, IsIntegralCurve f M (I x) (fun t => Φ t x) ∧ 0 ∈ I x ∧ Φ 0 x = x ∧ (uniqueness)
--   ```
--
--   so the range clause sits four levels deep behind `∀ x ∈ M`. Lean associates `∧` to the right, which makes the correct projection chain depend on how many right-nested pairs each definition has, and getting it wrong produces a projection error whose reported type is unhelpful. Publishing `flow_mem_of_mem` and `flow_comp_add_isIntegralCurve` names the two facts directly, so the Chapter 12 reductions need no projection arithmetic.
--
--   **Where it is used.** `TeschlODE.PeriodicOrbits.principal_matrix_solution` applies the zero-shift Jacobian identity at the base point `Φ t₀ x₀`, which requires `Φ t₀ x₀ ∈ M`; that is `flow_mem_of_mem` at `t := t₀`. The identity `TeschlODE.Shared.flow_periodic_orbit_global_everywhere` needs `Φ t₀ x₀ ∈ M` for the same reason, and its proof uses `flow_comp_add_isIntegralCurve` to apply the uniqueness clause of `IsMaximalFlow` at that point.
--
--   **Source.** Teschl, *Ordinary Differential Equations and Dynamical Systems* (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2, Eqs. (6.8)-(6.9); the translate form is the flow property (6.11). Both are definitional consequences of `IsIntegralCurve` and the chain rule, not analytic theorems.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2 Eq. (6.11)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- The translate `s ↦ Φ (s + c) x` is an integral curve of the same field on `I x - c`, so
uniqueness applies to it. This is the mechanism used to propagate `I x = ℝ` around a periodic
orbit, and to move the base point from `x₀` to `Φ t₀ x₀` in the Chapter 12 statements.

It is the flow property (6.11) in the form needed by §12: composing an integral curve with the
affine map `s ↦ s + c` stays an integral curve of the same field. -/
theorem flow_comp_add_isIntegralCurve {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : IsMaximalFlow f M I Φ) (x : Fin n → ℝ)
    (hx : x ∈ M) (c : ℝ) :
    IsIntegralCurve f M {s | s + c ∈ I x} (fun s => Φ (s + c) x) := by sorry

end TeschlODE.Shared
