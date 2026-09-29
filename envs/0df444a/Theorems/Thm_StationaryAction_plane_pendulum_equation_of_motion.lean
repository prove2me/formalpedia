-- Prove2me | Theorems.Thm_StationaryAction_plane_pendulum_equation_of_motion
-- name    : StationaryAction.plane_pendulum_equation_of_motion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:34:24.427683+00:00
-- url     : https://prove2.me/theorems/1f6430c8-512f-4d3e-8104-a3aee5b01371
-- title:
--   Lagrange equation of the plane pendulum
-- statement:
--   The second mechanical application in §3.1 of the source, and the one that shows the method is indifferent to the coordinate system: the plane pendulum in the angular coordinate $\theta$.
--
--   For a bob of mass $m$ on a rigid rod of length $\ell$ in a uniform gravitational field $g$, the kinetic and potential energies are $T = \tfrac{1}{2} m \ell^2 \dot\theta^2$ and $U = m g \ell (1 - \cos\theta)$, so the Lagrangian is
--
--   $$L(\theta, \dot\theta) = \tfrac{1}{2} m \ell^2 \dot\theta^2 - m g \ell\,(1 - \cos\theta).$$
--
--   Assume $m \neq 0$ and $\ell \neq 0$, and let $\theta$ be a twice continuously differentiable function of time. Then the Euler–Lagrange equation for $L$ holds at every $t \in [t_1,t_2]$ if and only if
--
--   $$\ddot\theta(t) + \frac{g}{\ell}\,\sin\theta(t) = 0 \qquad \text{for every } t \in [t_1,t_2],$$
--
--   which is equation (3.19) of the source — the exact pendulum equation, valid without the small-angle approximation.
--
--   **Formalization Note** The hypotheses $m \neq 0$ and $\ell \neq 0$ are exactly what is needed to divide the Euler–Lagrange equation by $m\ell^2$; they are not physical positivity assumptions and the statement does not require $g > 0$.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. §3.1, pp. 44–45, Eqs. (3.18)–(3.19).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, §3.1, Eqs. (3.18)–(3.19), plane pendulum. -/
theorem plane_pendulum_equation_of_motion
    (m g l : ℝ) (hm : m ≠ 0) (hl : l ≠ 0) (θ : ℝ → ℝ) (t₁ t₂ : ℝ) (hθ : ContDiff ℝ 2 θ) :
    (∀ t ∈ Set.Icc t₁ t₂,
        eulerLagrangeExpr
          (fun u v _ => m * l ^ 2 * v ^ 2 / 2 - m * g * l * (1 - Real.cos u)) θ t = 0) ↔
      ∀ t ∈ Set.Icc t₁ t₂, deriv (deriv θ) t + (g / l) * Real.sin (θ t) = 0 := by sorry

end StationaryAction
