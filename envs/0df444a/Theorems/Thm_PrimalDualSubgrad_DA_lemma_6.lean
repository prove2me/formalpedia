-- Prove2me | Theorems.Thm_PrimalDualSubgrad_DA_lemma_6
-- name    : PrimalDualSubgrad.DA.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:28.903002+00:00
-- url     : https://prove2.me/theorems/518c1b2b-0e1e-44be-9582-d563a9166afe
-- title:
--   Lemma 6 — a strongly convex function has a unique minimizer on Q, with quadratic growth
-- statement:
--   Let $Q$ be a nonempty closed convex set in a finite-dimensional real normed space $E$, and let $d$ be continuous on $Q$ and strongly convex on $Q$ with convexity parameter $\sigma > 0$: for all $x, y \in Q$, $\alpha \in [0,1]$, $d(\alpha x + (1-\alpha)y) \le \alpha d(x) + (1-\alpha)d(y) - \frac12\sigma\alpha(1-\alpha)\|x-y\|^2$ (9.3). Then the problem $\min_{x \in Q} d(x)$ (9.4) has a unique solution $x^*$, and for every $x \in Q$
--   $$d(x) \ge d(x^*) + \tfrac12 \sigma \|x - x^*\|^2. \qquad (9.5)$$
--
--   The lemma makes the prox-center and the argmin map $\pi_\beta$ well defined, and (9.5) applied to $-\langle s, \cdot\rangle + \beta d$ is the quadratic growth used in Lemma 1 and Theorem 1.
--
--   **Formalization Note** Nonemptiness of $Q$ and finite dimension of $E$ are implicit on the page (the proof starts from a nonempty level set; $E$ is finite-dimensional throughout the paper). The norm is arbitrary.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), p. 36, Lemma 6 (with Definition 1, (9.3), (9.4))

import Mathlib

namespace PrimalDualSubgrad.DA

/-- Lemma 6 (p. 36). Let `Q` be a nonempty closed convex set in a finite-dimensional real normed
space and `d` a function continuous on `Q` and strongly convex on `Q` with parameter `σ > 0`
(Definition 1, (9.3)). Then `min_{x ∈ Q} d(x)` (9.4) has a unique solution `x*`, and
`d(x) ≥ d(x*) + σ/2 ‖x − x*‖²` for every `x ∈ Q` (9.5). -/
theorem lemma_6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (d : E → ℝ) (σ : ℝ)
    (hQc : IsClosed Q) (hQconv : Convex ℝ Q) (hQne : Q.Nonempty)
    (hd : ContinuousOn d Q) (hσ : 0 < σ) (hsc : StrongConvexOn Q σ d) :
    (∃! xs : E, xs ∈ Q ∧ ∀ x ∈ Q, d xs ≤ d x) ∧
      ∀ xs ∈ Q, (∀ x ∈ Q, d xs ≤ d x) → ∀ x ∈ Q, d xs + σ / 2 * ‖x - xs‖ ^ 2 ≤ d x := by sorry

end PrimalDualSubgrad.DA
