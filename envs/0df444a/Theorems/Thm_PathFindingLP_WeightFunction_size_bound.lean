-- Prove2me | Theorems.Thm_PathFindingLP_WeightFunction_size_bound
-- name    : PathFindingLP.WeightFunction.size_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:47:13.425988+00:00
-- url     : https://prove2.me/theorems/b664835c-1d6e-4d5d-8e92-410d2d2cca39
-- title:
--   Theorem 1, Size: $\|g(s)\|_1\le 2\,\mathrm{rank}(A)$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank $n$ with $1\le n<m$, let $\alpha=1-\left(\log_2\frac{2m}{\mathrm{rank}(A)}\right)^{-1}$ and $\beta=\frac{\mathrm{rank}(A)}{2m}$, and let $s\in\mathbb R^m_{>0}$. If $w\in\mathbb R^m_{>0}$ minimizes the objective $\hat f(s,\cdot)$ of (6) over $\mathbb R^m_{>0}$, then
--
--   $$
--   \|w\|_1=\sum_{i\in[m]}|w_i|\le 2\,\mathrm{rank}(A).
--   $$
--
--   Applied to $w=g(s)$ this is the Size bullet of Theorem 1: the weight function of the paper has size constant $c_1(g)=2\,\mathrm{rank}(A)$, which is what makes the path-following method run in $\tilde O(\sqrt{\mathrm{rank}(A)})$ iterations rather than $\tilde O(\sqrt m)$.
--
--   **Formalization Note** The bullet "$c_1(g)=2\,\mathrm{rank}(A)$" is read, as in Definition 4, as the upper bound $\|g(s)\|_1\le c_1$. The statement is made for every minimizer, so it does not depend on how $g$ is chosen; existence and uniqueness of the minimizer is a separate item.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433 (DOI 10.1109/FOCS.2014.52), p. 429, §V.A, Theorem 1 (Properties of Weight Function), Size bullet

import Mathlib
import Definitions.Def_PathFindingLP_WeightFunction_RegularizedObjective

namespace PathFindingLP.WeightFunction
theorem size_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (w : Fin m → ℝ) (hw : IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s w) :
    ∑ i, |w i| ≤ 2 * (A.rank : ℝ) := by sorry
end PathFindingLP.WeightFunction
