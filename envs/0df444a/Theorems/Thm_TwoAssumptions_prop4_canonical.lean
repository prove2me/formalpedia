-- Prove2me | Theorems.Thm_TwoAssumptions_prop4_canonical
-- name    : TwoAssumptions.prop4_canonical
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T23:18:05.173033+00:00
-- url     : https://prove2.me/theorems/fd78e961-dda6-481e-aca0-aa9830d8a53a
-- title:
--   Proposition 4 — canonical variables make the density coordinate-invariant
-- statement:
--   **Proposition 4.** The density $\rho$ transforms both as a scalar and as a density under a change of state variables; the variables for which this holds are the **canonical variables**.
--
--   Under a change of variables $\hat\xi^b=\hat\xi^b(\xi^a)$ the density obeys $\rho(\xi^a)=\rho(\hat\xi^b)\,\bigl|\partial\hat\xi^b/\partial\xi^a\bigr|$. For canonical variables the Jacobian is unitary, $\bigl|\partial\hat\xi^b/\partial\xi^a\bigr|=1$, so the density is also invariant as a scalar: $\rho(\xi^a)=\rho(\hat\xi^b)$.
--
--   **Formalization Note.** The change of variables is a $C^1$ map $f$; the Jacobian factor is $|\det(df_x)|$ (`(fderiv ℝ f x).det`). The statement is the implication "unit Jacobian + density transformation rule $\Rightarrow$ scalar invariance", the converse direction of Proposition 5.
-- source:
--   Cosper 2022, From Two Assumptions to Hamilton's Mechanics, https://github.com/assumptionsofphysics/thesis-ClassicalMechanics, Proposition (4), §2.1.

import Mathlib
open scoped ContDiff

namespace TwoAssumptions

theorem prop4_canonical {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ))
    (ρ : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
    (hf : ContDiffAt ℝ 1 f x)
    (hJ : |(fderiv ℝ f x).det| = 1)
    (hdensity : ρ x = ρ (f x) * |(fderiv ℝ f x).det|) :
    ρ x = ρ (f x) := by sorry

end TwoAssumptions
