-- Prove2me | Theorems.Thm_PathFindingLP_WeightFunction_properties_of_weight_function
-- name    : PathFindingLP.WeightFunction.properties_of_weight_function
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:49:12.701235+00:00
-- url     : https://prove2.me/theorems/531dfc47-e201-4018-abc5-2bc34261eeb1
-- title:
--   Theorem 1 (Properties of Weight Function): the regularized D-optimal-design weights form a weight function
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank $n$ with $1\le n<m$. Pick
--
--   $$
--   \alpha=1-\left(\log_2\frac{2m}{\mathrm{rank}(A)}\right)^{-1},\qquad\beta=\frac{\mathrm{rank}(A)}{2m},
--   $$
--
--   and for $s\in\mathbb R^m_{>0}$ let $g(s)=\arg\min_{w\in\mathbb R^m_{>0}}\hat f(s,w)$ with
--
--   $$
--   \hat f(s,w)=\mathbb 1^\top w-\frac1\alpha\log\det\left(A_s^\top W^\alpha A_s\right)-\beta\sum_{i\in[m]}\log w_i,\qquad A_s=S^{-1}A.
--   $$
--
--   Then:
--
--   1. for every $s\in\mathbb R^m_{>0}$ the minimizer exists and is unique, so $g$ is well defined on $\mathbb R^m_{>0}$;
--   2. $g$ is a weight function in the sense of Definition 4 with constants
--   $$
--   c_1(g)=2\,\mathrm{rank}(A),\qquad c_\gamma(g)=2,\qquad c_r(g)=2\log_2\frac{2m}{\mathrm{rank}(A)};
--   $$
--   that is, $g$ is positive and differentiable on $\mathbb R^m_{>0}$, $\|g(s)\|_1\le 2\,\mathrm{rank}(A)$, $\gamma(s,g(s))\le2$, the two step-consistency inequalities hold for every $r\ge c_r(g)$, and $\|g(s)\|_\infty\le2$.
--
--   Combined with the paper's weighted path-following framework (Theorem 5 of §IV.C), this weight function yields an interior point method with $\tilde O(\sqrt{\mathrm{rank}(A)}\,L)$ iterations.
--
--   **Formalization Note** Part 2 is stated for every map $g:\mathbb R^m\to\mathbb R^m$ whose value at each positive $s$ is a minimizer of $\hat f(s,\cdot)$; by part 1 such a map exists and is unique on the orthant, and its values off the orthant play no role. The hypotheses $\mathrm{rank}(A)=n$, $n\ge1$ and $n<m$ are where the page's formulas are defined ($\beta>0$, $\log_2\frac{2m}{\mathrm{rank}(A)}>1$, so $\alpha\in(0,1)$). Size is read as an upper bound, as in Definition 4. Uniformity $\|g(s)\|_\infty\le2$ is part of Definition 4 and so part of the claim.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433 (DOI 10.1109/FOCS.2014.52), p. 429, §V.A, Theorem 1 (Properties of Weight Function); objective (6) p. 429; Definitions 2 and 4 p. 428

import Mathlib
import Definitions.Def_PathFindingLP_WeightFunction_RegularizedObjective
import Definitions.Def_PathFindingLP_WeightFunction_IsWeightFunction

namespace PathFindingLP.WeightFunction
theorem properties_of_weight_function {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) :
    (∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
        ∃! w : Fin m → ℝ, IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s w) ∧
      ∀ g : (Fin m → ℝ) → (Fin m → ℝ),
        (∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
          IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s (g s)) →
        IsWeightFunction A g (2 * (A.rank : ℝ)) 2
          (2 * Real.logb 2 (2 * (m : ℝ) / (A.rank : ℝ))) := by sorry
end PathFindingLP.WeightFunction
