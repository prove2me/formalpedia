-- Prove2me | Theorems.Thm_PolicyGradTheory_Softmax_softmax_linear_smoothness
-- name    : PolicyGradTheory.Softmax.softmax_linear_smoothness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:35:46.238722+00:00
-- url     : https://prove2.me/theorems/07ef2787-cba2-4bac-9354-d677bcfd921e
-- title:
--   Lemma D.1, pp. 70–71 — θ_s ↦ π_θ(·|s)·c is β-smooth with β = 5‖c‖_∞
-- statement:
--   Fix a finite nonempty action set $\mathcal A$ and a vector $c\in\mathbb R^{|\mathcal A|}$. For a parameter vector $\theta_s\in\mathbb R^{|\mathcal A|}$ of a single state let $\pi_\theta(\cdot\mid s)$ be the softmax probability vector, $\pi_\theta(a\mid s)=\exp(\theta_{s,a})/\sum_{a'}\exp(\theta_{s,a'})$, and define
--   $$
--   F(\theta_s)=\pi_\theta(\cdot\mid s)\cdot c=\sum_a\pi_\theta(a\mid s)\,c_a .
--   $$
--   Then for all $\theta_s,\theta'_s\in\mathbb R^{|\mathcal A|}$,
--   $$
--   \|\nabla_{\theta_s}F(\theta_s)-\nabla_{\theta_s}F(\theta'_s)\|_2\le\beta\,\|\theta_s-\theta'_s\|_2,\qquad \beta=5\|c\|_\infty ,
--   $$
--   where $\|c\|_\infty=\max_a|c_a|$.
--
--   The paper applies this with $c=A^{(t)}(s,\cdot)$ in the proof of Lemma C.2: it is what makes a small gradient step improve every state's expected advantage.
--
--   **Formalization Note** $\theta_s$ ranges over `EuclideanSpace ℝ A`, so the norms are Euclidean; $\|c\|_\infty$ is the maximum of $|c_a|$ over the nonempty finite set $\mathcal A$.
-- source:
--   arXiv:1908.00261v5, Lemma D.1, pp. 70–71 (F of (38), p. 60)

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
open FoundationsML.ReinforcementLearning Filter Topology

namespace PolicyGradTheory.Softmax

/-- Lemma D.1 (arXiv:1908.00261v5, pp. 70–71): for a fixed vector `c ∈ ℝ^{|A|}`, the function
`F(θ_s) = ∑_a softmax(θ_s)_a c_a` of the parameters `θ_s ∈ ℝ^{|A|}` of one state is
`β`-smooth in the Euclidean norm with `β = 5‖c‖_∞`. -/
theorem softmax_linear_smoothness {A : Type*} [Fintype A] [Nonempty A] (c : A → ℝ)
    (x x' : EuclideanSpace ℝ A) :
    ‖gradient (softmaxDot c) x - gradient (softmaxDot c) x'‖ ≤
      5 * Finset.univ.sup' Finset.univ_nonempty (fun a => |c a|) * ‖x - x'‖ := by sorry

end PolicyGradTheory.Softmax
