-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_sol_nonempty
-- name    : SparseLpLq.SmallP.sol_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:57.108447+00:00
-- url     : https://prove2.me/theorems/9b0601f1-56ea-414a-ba77-0b2ab1c71f93
-- title:
--   §1, p. 1 — SOL(A,b,σ,p,q) is nonempty for every 0 ≤ p ≤ 1 and 1 ≤ q ≤ ∞
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $\sigma\ge 0$ and $1\le q\le\infty$, and assume that the feasible set $\mathrm{FEA}(A,b,\sigma,q)=\{x : \|Ax-b\|_q\le\sigma\}$ is nonempty. Then for every $0\le p\le 1$ problem (1.1) has an optimal solution:
--
--   $$\mathrm{SOL}(A,b,\sigma,p,q)\neq\emptyset,\qquad 0\le p\le 1,\ 1\le q\le\infty .$$
--
--   Here the objective is $\|x\|_p^p=\sum_i|x_i|^p$ for $p>0$ and $\|x\|_0$, the number of nonzero entries, for $p=0$. The case $p=0$ concerns a sparsest feasible point.
--
--   This is the well-posedness statement of the paper: every result on the solution sets $\mathrm{SOL}(A,b,\sigma,p,1)$, in particular Theorem 2.2, presupposes that they are nonempty.
--
--   **Formalization Note** $q$ ranges over the extended reals $[1,\infty]$, with $q=\infty$ included. The paper's further blanket assumption $\|b\|_q>\sigma$ is stated on p. 1 after this existence claim and is not used by it, so it is not a hypothesis here.
--
--   Differences from the source: none.
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 1, §1 (existence of optimal solutions of problem (1.1))

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP
theorem sol_nonempty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (hσ : 0 ≤ σ) (hfeas : (FEA A b σ q).Nonempty)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (SOL A b σ p q).Nonempty := by sorry
end SparseLpLq.SmallP
