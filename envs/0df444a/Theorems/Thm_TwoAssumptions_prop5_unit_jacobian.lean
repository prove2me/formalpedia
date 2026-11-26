-- Prove2me | Theorems.Thm_TwoAssumptions_prop5_unit_jacobian
-- name    : TwoAssumptions.prop5_unit_jacobian
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T23:19:08.76727+00:00
-- url     : https://prove2.me/theorems/2303a2e0-b522-4ff7-8196-81c4addeff13
-- title:
--   Proposition 5 — canonical transformations have unitary Jacobian
-- statement:
--   **Proposition 5.** A change of canonical state variables is differentiable and has unitary Jacobian:
--   $$\left|\frac{\partial\hat\xi^b}{\partial\xi^a}\right|=1.$$
--   Such a transformation is a **canonical transformation**.
--
--   Because $\rho$ transforms as a density, $\rho(\xi^a)=\rho(\hat\xi^b)\,|J|$, and is coordinate-invariant as a scalar, $\rho(\xi^a)=\rho(\hat\xi^b)$, with $\rho>0$, the Jacobian factor must satisfy $|J|=1$.
--
--   **Formalization Note.** $|J|$ is $|\det(df_x)|$ for the $C^1$ change of variables $f$. The positivity hypothesis $\rho(x)>0$ rules out the degenerate case where the density vanishes and the Jacobian is unconstrained.
-- source:
--   Cosper 2022, From Two Assumptions to Hamilton's Mechanics, https://github.com/assumptionsofphysics/thesis-ClassicalMechanics, Proposition (5), §2.1.

import Mathlib
open scoped ContDiff

namespace TwoAssumptions

theorem prop5_unit_jacobian {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ))
    (ρ : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
    (hf : ContDiffAt ℝ 1 f x)
    (hρ : ρ x > 0)
    (hdensity : ρ x = ρ (f x) * |(fderiv ℝ f x).det|)
    (hscalar : ρ x = ρ (f x)) :
    |(fderiv ℝ f x).det| = 1 := by sorry

end TwoAssumptions
