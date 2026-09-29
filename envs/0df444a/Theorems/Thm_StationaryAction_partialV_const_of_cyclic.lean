-- Prove2me | Theorems.Thm_StationaryAction_partialV_const_of_cyclic
-- name    : StationaryAction.partialV_const_of_cyclic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:28:29.036213+00:00
-- url     : https://prove2.me/theorems/b348862f-41cd-48c0-a07b-1ed3f8371e52
-- title:
--   First integral for a cyclic coordinate
-- statement:
--   This is the conservation law Euler uses in *Additamentum II* and the source reproduces as equation (2.45): when the integrand does not depend on $y$, the momentum $\partial f/\partial y'$ is constant along a solution.
--
--   Let $f$ be twice continuously differentiable jointly, let $y$ be a twice continuously differentiable path, and suppose $\partial f/\partial y$ vanishes identically — the coordinate $y$ is *cyclic*. If $y$ satisfies the Euler–Lagrange equation at every point of $[x_1, x_2]$, then for every $x \in [x_1, x_2]$
--
--   $$\frac{\partial f}{\partial y'}\bigl(y(x), y'(x), x\bigr) = \frac{\partial f}{\partial y'}\bigl(y(x_1), y'(x_1), x_1\bigr).$$
--
--   In the source this is the step that reduces Euler's orbit problem to a first-order equation: since his integrand $Z$ does not contain the polar angle, $\partial Z/\partial p$ is a constant of the motion, and equation (2.46) — hence the orbit equation (2.39) obtained by the direct method — follows. In mechanical language it is the conservation of the momentum conjugate to an ignorable coordinate.
--
--   **Formalization Note** The conclusion is stated as equality with the value at the left endpoint rather than as the existence of a constant, which fixes the constant and keeps the statement usable without an existential.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. §2.7.1, pp. 35–36, Eqs. (2.44)–(2.46).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, §2.7.1, Eq. (2.45). -/
theorem partialV_const_of_cyclic
    (f : ℝ → ℝ → ℝ → ℝ) (y : ℝ → ℝ) (x₁ x₂ : ℝ)
    (hf : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (hy : ContDiff ℝ 2 y)
    (hcyclic : ∀ u v x : ℝ, partialY f u v x = 0)
    (hEL : ∀ x ∈ Set.Icc x₁ x₂, eulerLagrangeExpr f y x = 0) :
    ∀ x ∈ Set.Icc x₁ x₂,
      partialV f (y x) (deriv y x) x = partialV f (y x₁) (deriv y x₁) x₁ := by sorry

end StationaryAction
