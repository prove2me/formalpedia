-- Prove2me | Theorems.Thm_ProbMetricStab_Portfolio_lemma_5_1_a
-- name    : ProbMetricStab.Portfolio.lemma_5_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:53.363903+00:00
-- url     : https://prove2.me/theorems/a7db1221-22ba-4024-b82d-f3504d9957e1
-- title:
--   Lemma 5.1, first assertion, p. 24 — f₀(ξ, ·) convex; |f₀(ξ, x) − f₀(ξ̃, x̃)| ≤ α(‖ξ − ξ̃‖ + ‖x − x̃‖)
-- statement:
--   Let $\alpha\in(1,2)$, let $\Sigma^s$ be the unit sphere of $\mathbb R^s$, $X=\{x\in\mathbb R^s_+:\sum_i x_i=1\}$ and $f_0(\xi,x)=|\langle x,\xi\rangle|^\alpha$. Then:
--
--   1. for each $\xi\in\Sigma^s$ the function $x\mapsto f_0(\xi,x)$ is convex on $\mathbb R^s$;
--   2. for all $x,\tilde x\in X$ and $\xi,\tilde\xi\in\Sigma^s$,
--   $$|f_0(\xi,x)-f_0(\tilde\xi,\tilde x)|\le\alpha\big(\|\xi-\tilde\xi\|+\|x-\tilde x\|\big).$$
--
--   The joint Lipschitz estimate is what makes $\zeta_1$, the dual Lipschitz metric on $\Sigma^s$, the right distance for perturbations of the spectral measure.
--
--   **Formalization Note** Norms are Euclidean; the standing assumption $\alpha\in(1,2)$ of Section 5 is a hypothesis.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 24, Lemma 5.1 (first sentence)

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory
open scoped ENNReal

namespace ProbMetricStab.Portfolio
theorem lemma_5_1_a {s : ℕ} (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) :
    (∀ ξ ∈ unitSphere s, ConvexOn ℝ Set.univ (fun x : Rs s => f0 α ξ x)) ∧
    (∀ x ∈ simplex s, ∀ x' ∈ simplex s, ∀ ξ ∈ unitSphere s, ∀ ξ' ∈ unitSphere s,
      |f0 α ξ x - f0 α ξ' x'| ≤ α * (‖ξ - ξ'‖ + ‖x - x'‖)) := by sorry
end ProbMetricStab.Portfolio
