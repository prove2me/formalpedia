-- Prove2me | Theorems.Thm_StationaryAction_euler_lagrange_of_stationary_action
-- name    : StationaryAction.euler_lagrange_of_stationary_action
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:05:27.401042+00:00
-- url     : https://prove2.me/theorems/0dfaac77-ee00-4b7d-a315-47aa6da745b8
-- title:
--   Euler–Lagrange equation from the principle of stationary action
-- statement:
--   This is the central derivation of Chapter 3 of the source: the Euler–Lagrange equation is a consequence of the stationarity of the action.
--
--   Let $x_1 < x_2$ be real numbers, let the integrand $f(y, y', x)$ be twice continuously differentiable as a function of its three arguments jointly, and let $y : \mathbb{R} \to \mathbb{R}$ be a twice continuously differentiable path. Suppose $y$ makes the action
--
--   $$S[y] = \int_{x_1}^{x_2} f\bigl(y(x), y'(x), x\bigr)\,dx$$
--
--   stationary, in the sense that for every twice continuously differentiable $\eta$ with $\eta(x_1) = \eta(x_2) = 0$ the function $\alpha \mapsto S[y + \alpha\eta]$ has vanishing derivative at $\alpha = 0$. Then for every $x$ in the closed interval $[x_1, x_2]$,
--
--   $$\frac{\partial f}{\partial y}\bigl(y(x), y'(x), x\bigr) - \frac{d}{dx}\left[\frac{\partial f}{\partial y'}\bigl(y(x), y'(x), x\bigr)\right] = 0.$$
--
--   This is equation (3.9) of the source. Substituting the independent variable $x$ by time $t$, the path $y$ by a generalised coordinate $q$, and the integrand $f$ by the Lagrangian $L = T - U$, it becomes Hamilton's principle of stationary action and equation (3.17), the Lagrange equation of motion — the statement from which the monograph recovers the harmonic oscillator and the plane pendulum without writing down a single force.
--
--   **Formalization Note** Stationarity is quantified over all admissible variations, the conclusion holds at every point of the closed interval (not almost everywhere), and the $C^2$ hypotheses on $f$ and on $y$ are what make the derivative of $x \mapsto \partial f/\partial y'(y(x), y'(x), x)$ an honest derivative.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. Chapter 3, pp. 38–40, Eqs. (3.1)–(3.9); §3.1, p. 44, Eq. (3.17).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, Chapter 3, Eq. (3.9) / Eq. (3.17). -/
theorem euler_lagrange_of_stationary_action
    (f : ℝ → ℝ → ℝ → ℝ) (y : ℝ → ℝ) (x₁ x₂ : ℝ) (hx : x₁ < x₂)
    (hf : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (hy : ContDiff ℝ 2 y)
    (hstat : IsStationaryPath f y x₁ x₂) :
    ∀ x ∈ Set.Icc x₁ x₂, eulerLagrangeExpr f y x = 0 := by sorry

end StationaryAction
