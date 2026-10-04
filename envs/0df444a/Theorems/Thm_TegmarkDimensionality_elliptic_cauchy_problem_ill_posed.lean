-- Prove2me | Theorems.Thm_TegmarkDimensionality_elliptic_cauchy_problem_ill_posed
-- name    : TegmarkDimensionality.elliptic_cauchy_problem_ill_posed
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T09:01:42.798282+00:00
-- url     : https://prove2.me/theorems/f3bfcc8f-ff81-4c2c-9533-9d8e73701261
-- title:
--   Cauchy problem for the Laplace equation with data on a line is ill-posed
-- statement:
--   There is a sequence of $C^2$ functions $u_k:\mathbb R^2\to\mathbb R$, $k=0,1,2,\dots$, such that:
--
--   1. each $u_k$ solves the Laplace equation $\partial_x^2u_k+\partial_y^2u_k=0$ on $\mathbb R^2$;
--   2. the Cauchy data on the line $y=0$ tend to zero uniformly: for every $\varepsilon>0$ there is $K$ with $|u_k(x,0)|\le\varepsilon$ and $|\partial_yu_k(x,0)|\le\varepsilon$ for all $k\ge K$ and all $x\in\mathbb R$;
--   3. off the line the solutions blow up: for every $y\neq0$ and every $M$ there is $K$ such that for every $k\ge K$ some $x$ has $|u_k(x,y)|>M$.
--
--   So arbitrarily small changes in the data on the line $y=0$ produce arbitrarily large changes in the solution at any distance from it. An observer in a world with no time dimension ($m=0$, elliptic field equations) can make no inferences from local data.
--
--   **Formalization Note** The statement is the simplest instance of the paper's claim: the two-dimensional Laplace equation with data on a line.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L73, fifth paragraph ('giving initial data for an elliptic PDE on a non-closed hypersurface, say a plane, is an ill-posed problem'); classical example of Hadamard, cf. Courant–Hilbert vol. II

import Mathlib

namespace TegmarkDimensionality

/-- Initial data on the line `y = 0` for the Laplace equation `u_xx + u_yy = 0` in the plane
is an ill-posed problem: there are smooth solutions `u_k` whose Cauchy data
`u_k(x,0), ∂_y u_k(x,0)` tend to `0` uniformly in `x`, while for every `y ≠ 0` the solutions
`u_k(·, y)` become unbounded (their supremum over `x` tends to infinity). -/
theorem elliptic_cauchy_problem_ill_posed :
    ∃ u : ℕ → ℝ → ℝ → ℝ,
      (∀ k, ContDiff ℝ 2 (fun p : ℝ × ℝ => u k p.1 p.2)) ∧
      (∀ k x y, deriv (fun x' => deriv (fun x'' => u k x'' y) x') x +
          deriv (fun y' => deriv (fun y'' => u k x y'') y') y = 0) ∧
      (∀ ε > 0, ∃ K, ∀ k ≥ K, ∀ x,
          |u k x 0| ≤ ε ∧ |deriv (fun y => u k x y) 0| ≤ ε) ∧
      (∀ y ≠ 0, ∀ M : ℝ, ∃ K, ∀ k ≥ K, ∃ x, M < |u k x y|) := by sorry

end TegmarkDimensionality
