-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_bernstein_derivatives
-- name    : ShapeSOS.ConvexConsistency.bernstein_derivatives
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:22:37.954892+00:00
-- url     : https://prove2.me/theorems/717714d3-e6b4-4382-9e97-c366699d9f77
-- title:
--   Lemma B.5 — uniform convergence of the printed Bernstein mixed derivatives
-- statement:
--   Let $n\ge1$, let $m\ge0$ be an integer, and let $f$ be $m$ times continuously differentiable on $[0,1]^n$. Form $B_d$ using exactly the sum over $j_1+\cdots+j_n=d$ printed in Lemma B.5. For every nonnegative multi-index $k$ with $\sum_i k_i\le m$, the source asserts
--   $$\lim_{d\to\infty}\sup_{x\in[0,1]^n}|\partial^k B_d(f,x)-\partial^k f(x)|=0.$$
--   This is the smooth approximation support for Proposition 3.11. The printed index set is retained; the counterexample at $n=1,f=1$ is recorded separately in I4.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - encoding: smoothness on a closed box → ContDiffOn and coordinate fderivWithin on that box; reason: within-domain derivatives preserve the interior derivatives and their continuous boundary values
--   - encoding: nonnegative derivative orders written as an integer m and |k_i| → natural orders m and k_i, and binomial coefficients Nat.choose; reason: negative derivative orders are undefined; for nonnegative orders absolute values equal the orders
--   - encoding: a limit as d tends to infinity of j_i/d evaluations → division by zero gives zero at the unused initial index d=0; reason: changing a single initial term does not change the limit
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 26, Lemma B.5

import Definitions.Def_ShapeSOS_ConvexConsistency_Approximation

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem bernstein_derivatives (n : ℕ) (hn : 0 < n) (m : ℕ)
    (f : Vec n → ℝ) (hf : ContDiffOn ℝ m f (cube n 0 1)) :
    ∀ k : Fin n → ℕ, (∑ i, k i) ≤ m →
      Tendsto (fun d => uniformError (cube n 0 1)
        (mixedPartial (cube n 0 1) k (value (bernstein d f)))
        (mixedPartial (cube n 0 1) k f)) atTop (𝓝 0) := by sorry

end ShapeSOS.ConvexConsistency
