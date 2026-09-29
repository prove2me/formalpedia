-- Prove2me | Theorems.Thm_RelaxationMethod_FullDim_theorem1
-- name    : RelaxationMethod.FullDim.theorem1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:27:34.741858+00:00
-- url     : https://prove2.me/theorems/14064d3f-f9c5-4477-8bf4-4eaf808e5114
-- title:
--   Theorem 1 — relaxation converges to the boundary and reflexion terminates when $A$ is full-dimensional
-- statement:
--   Let $A = \bigcap_{i=1}^m \{x \in E_n : \sum_j a_{ij}x_j + b_i \ge 0\}$ be the solution polytope of a consistent system of linear inequalities, and assume that $A$ has dimension $r = n$, i.e. $A$ is not contained in any hyperplane of $E_n$. Let $\{p_\nu\}$ be a sequence obtained by the relaxation process: $p_{\nu+1}$ arises from $p_\nu$ by a relaxation step with parameter $\lambda$ as long as $p_\nu \notin A$.
--
--   1. **Case 1.** If $0 < \lambda < 2$, then either the process terminates ($p_N \in A$ for some $N$) or else
--   $$
--   \lim_{\nu\to\infty} p_\nu = l \quad \text{for a point } l \text{ on the boundary of } A .
--   $$
--   2. **Case 2.** If $\lambda = 2$ (the reflexion method), the process always terminates: $p_N \in A$ for some $N$.
--
--   Both cases hold for every starting point $p_0$ and every choice of the farthest half-space at every step. Case 1 is Agmon's convergence theorem; Case 2, finite termination of the reflexion method for a full-dimensional solution set, is the main new result of the paper.
--
--   **Formalization Note** "Consistent" is the hypothesis that $A$ is nonempty (the paper assumes it "from the outset"); $r = n$ is `affineSpan ℝ A = ⊤`; "boundary" is `frontier A`; convergence is `Tendsto p atTop (𝓝 l)`. The paper's pre-assigned tie-breaking rule is replaced by allowing any maximizing index at every step, which makes the statement at least as strong as the paper's. The parameter $\lambda$ is named `lam`.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 395, Theorem 1, Cases 1 and 2

import Mathlib
import Definitions.Def_RelaxationMethod_FullDim_RelaxStep
import Definitions.Def_RelaxationMethod_FullDim_FejerMonotone
open Filter Topology

namespace RelaxationMethod.FullDim

/-- Theorem 1, p. 395. Let the solution polytope `A` of (1.2) be nonempty and not contained in
any hyperplane (`r = n`). Case 1: for `0 < lam < 2` every run of the relaxation process either
terminates (reaches `A`) or converges to a point on the boundary of `A`. Case 2: for `lam = 2`
(the reflexion method) every run terminates. -/
theorem theorem1 {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (hr : affineSpan ℝ (polytope a b) = ⊤) :
    (∀ lam : ℝ, 0 < lam → lam < 2 → ∀ p : ℕ → EuclideanSpace ℝ (Fin n),
        IsRelaxRun a b lam p →
          (∃ N : ℕ, p N ∈ polytope a b) ∨
            ∃ l ∈ frontier (polytope a b), Tendsto p atTop (𝓝 l)) ∧
    (∀ p : ℕ → EuclideanSpace ℝ (Fin n), IsRelaxRun a b 2 p →
        ∃ N : ℕ, p N ∈ polytope a b) := by sorry

end RelaxationMethod.FullDim
