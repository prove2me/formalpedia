-- Prove2me | Theorems.Thm_StabilityDichotomies_Approximability_finite_bernoulli_influence_derivative
-- name    : StabilityDichotomies.Approximability.finite_bernoulli_influence_derivative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:12:26.333561+00:00
-- url     : https://prove2.me/theorems/3236579d-6814-47f4-b155-50cb0e490ccc
-- title:
--   Derivative of a Bernoulli product expectation equals the sum of influences
-- statement:
--   Let $C$ be a finite set and let $h:\{0,1\}^C\to\mathbb R$ be arbitrary. For each real $p$, define $F(p)=\sum_x h(x)\prod_{i\in C}p^{x_i}(1-p)^{1-x_i}$. Then $F$ is differentiable, and $$F'(p)=\sum_{i\in C}\sum_x\left(\prod_{j\in C}p^{x_j}(1-p)^{1-x_j}\right)\bigl(h(x^{i\leftarrow1})-h(x^{i\leftarrow0})\bigr).$$ For $p\in[0,1]$, the inner sum is the expected effect of forcing coordinate $i$ present instead of absent. This is the finite-product derivative identity in the sensitivity proof of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.17.

import Mathlib
noncomputable section
open scoped Classical BigOperators

namespace StabilityDichotomies.Approximability
theorem finite_bernoulli_influence_derivative {ι : Type} [Fintype ι]
    (h : (ι → Bool) → ℝ) (t : ℝ) :
    HasDerivAt (fun p => ∑ x : ι → Bool, h x * ∏ i : ι, (if x i then p else 1 - p))
      (∑ i : ι, ∑ x : ι → Bool, (∏ j : ι, (if x j then t else 1 - t)) *
        (h (Function.update x i true) - h (Function.update x i false))) t := by sorry
end StabilityDichotomies.Approximability
