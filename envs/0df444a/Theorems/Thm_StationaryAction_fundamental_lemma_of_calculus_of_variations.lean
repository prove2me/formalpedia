-- Prove2me | Theorems.Thm_StationaryAction_fundamental_lemma_of_calculus_of_variations
-- name    : StationaryAction.fundamental_lemma_of_calculus_of_variations
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:14:45.607838+00:00
-- url     : https://prove2.me/theorems/393d8bc6-cfd5-4f75-af71-459907e0fdcd
-- title:
--   Fundamental lemma of the calculus of variations
-- statement:
--   This is the step that carries the derivation of Chapter 3 from equation (3.8) to equation (3.9): a continuous coefficient that integrates to zero against every admissible variation vanishes identically.
--
--   Let $x_1 < x_2$ and let $g$ be continuous on $[x_1, x_2]$. Suppose that for every twice continuously differentiable $\eta$ with $\eta(x_1) = \eta(x_2) = 0$,
--
--   $$\int_{x_1}^{x_2} \eta(x)\,g(x)\,dx = 0 .$$
--
--   Then $g(x) = 0$ for every $x \in [x_1, x_2]$.
--
--   The source asserts this passage in words — the variation $\eta$ is arbitrary, so the bracket must vanish — and it is the only genuinely non-algebraic ingredient of the derivation. It is stated separately because it is reusable by every variational argument, and because its proof requires constructing $C^2$ test functions concentrated near a point.
--
--   **Formalization Note** The class of test functions is exactly the admissible variations of this mission: $C^2$ on the real line with both endpoint values zero. The conclusion covers the endpoints, which is where continuity of $g$ on the closed interval is used.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. Chapter 3, pp. 39–40, passage between Eqs. (3.8) and (3.9).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, Chapter 3, step from Eq. (3.8) to Eq. (3.9). -/
theorem fundamental_lemma_of_calculus_of_variations
    (g : ℝ → ℝ) (x₁ x₂ : ℝ) (hx : x₁ < x₂)
    (hg : ContinuousOn g (Set.Icc x₁ x₂))
    (h : ∀ η : ℝ → ℝ, IsAdmissibleVariation η x₁ x₂ → (∫ x in x₁..x₂, η x * g x) = 0) :
    ∀ x ∈ Set.Icc x₁ x₂, g x = 0 := by sorry

end StationaryAction
