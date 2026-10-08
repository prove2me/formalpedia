-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_mem_of_mem
-- name    : TeschlODE.Shared.flow_mem_of_mem
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T18:53:03.812961+00:00
-- url     : https://prove2.me/theorems/b3c15759-ef1b-47f6-847b-a7d4e98f64a6
-- title:
--   The flow maps each maximal interval into M
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
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2 Eqs. (6.8)-(6.9)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- Teschl, §6.2, p. 189, Eqs. (6.8)-(6.9): the flow maps each `I x` into `M`.

If `Φ` is the maximal flow of `ẋ = f(x)` on the open set `M`, then for every `x ∈ M` and every
`t ∈ I x` the point `Φ t x` lies in `M`. -/
theorem flow_mem_of_mem {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ))
    (hM : IsOpen M) (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (x : Fin n → ℝ) (hx : x ∈ M) (t : ℝ) (ht : t ∈ I x) :
    Φ t x ∈ M := by sorry

end TeschlODE.Shared
