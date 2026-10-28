-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_theorem_2_2
-- name    : SparseLpLq.SmallP.theorem_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:46:01.63188+00:00
-- url     : https://prove2.me/theorems/36a12f56-d540-40c3-8b9a-8d41c5a35b78
-- title:
--   Theorem 2.2, p. 8 — for small p > 0 the Lp-L1 solution set lies in the L0-L1 solution set and is constant on (0, p̄]
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\sigma\ge 0$ satisfy the paper's blanket assumptions for $q=1$: the feasible set $\mathrm{FEA}(A,b,\sigma,1)=\{x : \|Ax-b\|_1\le\sigma\}$ is nonempty and $\|b\|_1>\sigma$. For $0\le p\le 1$ let $\mathrm{SOL}(A,b,\sigma,p,1)$ be the set of optimal solutions of
--
--   $$\min_{x\in\mathbb R^n}\ \|x\|_p^p\quad\text{s.t.}\quad \|Ax-b\|_1\le\sigma, \tag{1.4}$$
--
--   where $\|x\|_p^p=\sum_i|x_i|^p$ for $p>0$ and $\|x\|_0$ is the number of nonzero entries. Then:
--
--   1. there exists $p^*\in(0,1]$ such that
--   $$\mathrm{SOL}(A,b,\sigma,p,1)\subseteq\mathrm{SOL}(A,b,\sigma,0,1)\quad\text{for every } p\in(0,p^*);$$
--   2. moreover, for this $p^*$ there exists $\bar p\in(0,p^*)$ such that
--   $$\mathrm{SOL}(A,b,\sigma,p,1)=\mathrm{SOL}(A,b,\sigma,\bar p,1)\quad\text{for every } p\in(0,\bar p].$$
--
--   No condition on $A$ (such as a restricted isometry or null space property) is assumed. The first clause says that solving the nonconvex $\ell_p$ problem with any sufficiently small $p>0$ yields a sparsest feasible point; the second says that the solution set stops changing once $p$ is small enough.
--
--   Differences from the source: none.
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 8, Theorem 2.2; proof pp. 8–9

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP
theorem theorem_2_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b) :
    ∃ pstar ∈ Set.Ioc (0 : ℝ) 1,
      (∀ p ∈ Set.Ioo 0 pstar, SOL A b σ p 1 ⊆ SOL A b σ 0 1) ∧
        ∃ pbar ∈ Set.Ioo 0 pstar, ∀ p ∈ Set.Ioc 0 pbar, SOL A b σ p 1 = SOL A b σ pbar 1 := by sorry
end SparseLpLq.SmallP
