-- Prove2me | Theorems.Thm_StationaryAction_first_variation_of_action
-- name    : StationaryAction.first_variation_of_action
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:22:08.959631+00:00
-- url     : https://prove2.me/theorems/8d940cfb-8560-452f-b610-7d8f50f12746
-- title:
--   First variation of the action
-- statement:
--   This is equation (3.5) of the source: differentiating the action of the varied path under the integral sign.
--
--   Let $x_1 \le x_2$, let the integrand $f(y, y', x)$ be twice continuously differentiable jointly in its three arguments, and let the path $y$ and the variation $\eta$ be twice continuously differentiable. Then
--
--   $$\left.\frac{d}{d\alpha}\int_{x_1}^{x_2} f\bigl(y + \alpha\eta,\ y' + \alpha\eta',\ x\bigr) dx\right|_{\alpha=0} = \int_{x_1}^{x_2} \left( \eta\,\frac{\partial f}{\partial y} + \eta'\,\frac{\partial f}{\partial y'} \right) dx,$$
--
--   the partial derivatives being evaluated along the unvaried path, at $\bigl(y(x), y'(x), x\bigr)$.
--
--   This is the analytic content of the chain-rule computation displayed in the source just before equation (3.5), and the point at which differentiation and integration are interchanged — a step the source performs silently. No endpoint condition on $\eta$ is needed here; it is needed only at the subsequent integration by parts.
--
--   **Formalization Note** The identity is stated for the oriented interval integral, so it is also meaningful (and asserted) in the degenerate case $x_1 = x_2$, where both sides are zero.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. Chapter 3, p. 39, Eqs. (3.3)–(3.5).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, Chapter 3, Eq. (3.5). -/
theorem first_variation_of_action
    (f : ℝ → ℝ → ℝ → ℝ) (y η : ℝ → ℝ) (x₁ x₂ : ℝ) (hx : x₁ ≤ x₂)
    (hf : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 2 η) :
    deriv (fun a : ℝ => action f (vary y η a) x₁ x₂) 0 =
      ∫ x in x₁..x₂, (η x * partialY f (y x) (deriv y x) x
        + deriv η x * partialV f (y x) (deriv y x) x) := by sorry

end StationaryAction
