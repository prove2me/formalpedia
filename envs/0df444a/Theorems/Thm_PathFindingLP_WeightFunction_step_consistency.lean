-- Prove2me | Theorems.Thm_PathFindingLP_WeightFunction_step_consistency
-- name    : PathFindingLP.WeightFunction.step_consistency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:48:43.829779+00:00
-- url     : https://prove2.me/theorems/b6f40cf0-30eb-4b89-ae72-8eb820938bc7
-- title:
--   Theorem 1, Step Consistency: $c_r(g)=2\log_2(2m/\mathrm{rank}(A))$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank $n$ with $1\le n<m$, let $\alpha=1-\left(\log_2\frac{2m}{\mathrm{rank}(A)}\right)^{-1}$ and $\beta=\frac{\mathrm{rank}(A)}{2m}$, and let $g:\mathbb R^m\to\mathbb R^m$ be any map such that, for every $s\in\mathbb R^m_{>0}$, $g(s)$ minimizes the objective $\hat f(s,\cdot)$ of (6) over $\mathbb R^m_{>0}$. Write $c_r=2\log_2\frac{2m}{\mathrm{rank}(A)}$, $G(s)=\mathrm{diag}(g(s))$, $G'(s)$ for the Jacobian of $g$ at $s$, and $S=\mathrm{diag}(s)$. Then $g$ is differentiable at every $s\in\mathbb R^m_{>0}$, $c_r\ge1$, and for every $s\in\mathbb R^m_{>0}$, every $r\ge c_r$ and every $y\in\mathbb R^m$,
--
--   $$
--   \left\|y+r^{-1}G(s)^{-1}G'(s)Sy\right\|_{G(s)}\le\|y\|_{G(s)}
--   \quad\text{and}\quad
--   \left\|y+r^{-1}G(s)^{-1}G'(s)Sy\right\|_\infty\le\|y\|_\infty+c_r\|y\|_{G(s)},
--   $$
--
--   where $\|y\|_{G(s)}=\sqrt{\sum_i g_i(s)y_i^2}$.
--
--   This is the Step Consistency bullet of Theorem 1: after a Newton step changes the slacks, resetting the weights to $g(s)$ does not undo the progress in centrality.
--
--   **Formalization Note** The first inequality is the operator-norm bound $\|I+r^{-1}G^{-1}G'S\|_{G(s)}\le1$ of Definition 4 written for every $y$. Differentiability is a conclusion, as in Definition 4 ("a differentiable function"); the Jacobian is `fderiv ℝ g s`. Because the hypothesis constrains $g$ only on the open orthant, the conclusion does not depend on how $g$ is chosen elsewhere.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433 (DOI 10.1109/FOCS.2014.52), p. 429, §V.A, Theorem 1 (Properties of Weight Function), Step Consistency bullet; Step Consistency from p. 428, §IV.C, Definition 4

import Mathlib
import Definitions.Def_PathFindingLP_WeightFunction_RegularizedObjective
import Definitions.Def_PathFindingLP_WeightFunction_IsWeightFunction

namespace PathFindingLP.WeightFunction
theorem step_consistency {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) (g : (Fin m → ℝ) → (Fin m → ℝ))
    (hg : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
      IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s (g s)) :
    (∀ s : Fin m → ℝ, (∀ i, 0 < s i) → DifferentiableAt ℝ g s) ∧
      IsStepConsistent g (2 * Real.logb 2 (2 * (m : ℝ) / (A.rank : ℝ))) := by sorry
end PathFindingLP.WeightFunction
