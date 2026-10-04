-- Prove2me | Theorems.Thm_ShorNonsmooth_SubgradMethod_constant_step_subsequence_near_optimal
-- name    : ShorNonsmooth.SubgradMethod.constant_step_subsequence_near_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:01:35.510989+00:00
-- url     : https://prove2.me/theorems/f57b5c8f-a050-4c9f-9768-7090ffbc0563
-- title:
--   Theorem 2.1, Corollary 1 — a step length $h_\delta$ gives a subsequence with $f(x_{k_i}) - f^* < \delta$
-- statement:
--   Let $f$ be a convex function on $E_n$ with a nonempty set $M^*$ of minimum points and let $f^* = \min_{x \in E_n} f(x)$. For every $\delta > 0$ there is a step length $h_\delta > 0$ with the following property. For every starting point $x_0$ and every choice of subgradients $g_f(x_k)$, the method
--   $$
--   x_{k+1} = x_k - h_\delta\,\frac{g_f(x_k)}{\|g_f(x_k)\|}
--   $$
--   either reaches a point $x_{k^*} \in M^*$, or has a subsequence $k_1 < k_2 < k_3 < \dots$ with
--   $$
--   f(x_{k_i}) - f^* < \delta \quad \text{for all } i.
--   $$
--
--   This turns the geometric statement of Theorem 2.1 into an approximation guarantee in function value.
--
--   **Formalization Note** $h_\delta$ is chosen before the subgradient selection and the starting point, so it depends only on $f$ and $\delta$, as in the book's derivation from Theorem 2.1. $f^*$ is written as the infimum of $f$, which is attained because $M^*$ is nonempty.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 24, Corollary 1 (to Theorem 2.1)

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace ShorNonsmooth.SubgradMethod

/-- Shor (1985), p. 24, Corollary 1 (of Theorem 2.1). Let `f` be convex on `E_n` with a nonempty
set `M*` of minimum points and `f* = min f`. For any `δ > 0` there is `h_δ > 0` (depending only on
`f` and `δ`) such that the subgradient method with stepsizes `h_{k+1}(x_k) = h_δ / ‖g_f(x_k)‖`,
for every subgradient selection and every start `x₀`, either hits `M*` at some `x_{k*}` or has a
subsequence `k₁ < k₂ < …` with `f(x_{k_i}) - f* < δ`. -/
theorem constant_step_subsequence_near_optimal {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hM : (MinSet f).Nonempty) :
    ∀ δ > 0, ∃ hδ > 0, ∀ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) → ∀ x₀ : EuclideanSpace ℝ (Fin n),
        (∃ kstar : ℕ, normalizedIter g (fun _ => hδ) x₀ kstar ∈ MinSet f) ∨
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ i, f (normalizedIter g (fun _ => hδ) x₀ (φ i)) - (⨅ y, f y) < δ := by sorry

end ShorNonsmooth.SubgradMethod
