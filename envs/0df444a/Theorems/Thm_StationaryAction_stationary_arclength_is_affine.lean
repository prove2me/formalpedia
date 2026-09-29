-- Prove2me | Theorems.Thm_StationaryAction_stationary_arclength_is_affine
-- name    : StationaryAction.stationary_arclength_is_affine
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:29:15.553163+00:00
-- url     : https://prove2.me/theorems/31eb3ae0-64d8-40af-8e38-4ba93b0ac001
-- title:
--   The shortest path between two points is a straight line
-- statement:
--   This is the worked example that closes Chapter 3 of the source: the stationary paths of the arc-length functional are the straight lines.
--
--   The length of the graph of $y$ over $[x_1, x_2]$ is
--
--   $$L[y] = \int_{x_1}^{x_2} \sqrt{1 + y'(x)^2}\,dx,$$
--
--   i.e. the action for the integrand $f(y, y', x) = \sqrt{1 + (y')^2}$, which does not depend on $y$ or on $x$. If $x_1 < x_2$, $y$ is twice continuously differentiable and $y$ makes this functional stationary against all admissible variations, then there are constants $c$ and $b$ with
--
--   $$y(x) = c\,x + b \qquad \text{for all } x \in [x_1,x_2].$$
--
--   The source reaches this through equations (3.10)–(3.13): $\partial f/\partial y = 0$, so $\partial f/\partial y' = y'/\sqrt{1+(y')^2}$ is constant, whence $y'$ is constant and $y$ is affine. It is the first non-trivial consequence of the Euler–Lagrange equation in the monograph, and the one that motivates the question it raises next: whether the shortest path is also the fastest.
--
--   **Formalization Note** The conclusion is an affine formula valid on $[x_1,x_2]$; nothing is claimed about $y$ outside that interval, where the stationarity hypothesis says nothing.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. Chapter 3, pp. 41–42, Eqs. (3.10)–(3.13).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, Chapter 3, Eqs. (3.10)–(3.13). -/
theorem stationary_arclength_is_affine
    (y : ℝ → ℝ) (x₁ x₂ : ℝ) (hx : x₁ < x₂) (hy : ContDiff ℝ 2 y)
    (hstat : IsStationaryPath (fun _ v _ => Real.sqrt (1 + v ^ 2)) y x₁ x₂) :
    ∃ c b : ℝ, ∀ x ∈ Set.Icc x₁ x₂, y x = c * x + b := by sorry

end StationaryAction
