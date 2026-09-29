-- Prove2me | Theorems.Thm_StationaryAction_harmonic_oscillator_equation_of_motion
-- name    : StationaryAction.harmonic_oscillator_equation_of_motion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:30:39.456283+00:00
-- url     : https://prove2.me/theorems/b117a0ae-d82d-4886-85d7-f60663064bba
-- title:
--   Lagrange equation of the one-dimensional harmonic oscillator
-- statement:
--   The first mechanical application in §3.1 of the source: the Lagrange equation of the one-dimensional harmonic oscillator is Newton's equation.
--
--   For a mass $m$ on a spring of stiffness $k$, the Lagrangian is
--
--   $$L(q, \dot q) = \tfrac{1}{2} m \dot q^2 - \tfrac{1}{2} k q^2 .$$
--
--   For a twice continuously differentiable trajectory $q$ and any time interval $[t_1, t_2]$, the Euler–Lagrange equation for $L$ holds at every $t \in [t_1,t_2]$ if and only if
--
--   $$m\,\ddot q(t) + k\,q(t) = 0 \qquad \text{for every } t \in [t_1,t_2].$$
--
--   The source computes $\partial L/\partial q = -kq$, $\partial L/\partial\dot q = m\dot q$ and concludes with the equation of motion, remarking that it is identical to what Newtonian mechanics gives, with no force ever written down. (The printed equation at that point reads $m\ddot x + x = 0$; the spring constant is missing there, and the statement formalised here restores it, as the immediately preceding partial derivatives require.)
--
--   **Formalization Note** The statement is an equivalence, so it also asserts that a trajectory obeying Newton's equation satisfies the Euler–Lagrange equation. No assumption is made on $m$ or $k$; in particular the degenerate case $m = k = 0$ makes both sides hold trivially.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. §3.1, p. 44, harmonic-oscillator example following Eq. (3.17).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, §3.1, one-dimensional harmonic oscillator. -/
theorem harmonic_oscillator_equation_of_motion
    (m k : ℝ) (q : ℝ → ℝ) (t₁ t₂ : ℝ) (hq : ContDiff ℝ 2 q) :
    (∀ t ∈ Set.Icc t₁ t₂,
        eulerLagrangeExpr (fun u v _ => m * v ^ 2 / 2 - k * u ^ 2 / 2) q t = 0) ↔
      ∀ t ∈ Set.Icc t₁ t₂, m * deriv (deriv q) t + k * q t = 0 := by sorry

end StationaryAction
