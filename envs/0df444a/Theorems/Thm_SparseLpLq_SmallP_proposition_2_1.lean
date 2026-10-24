-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_proposition_2_1
-- name    : SparseLpLq.SmallP.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:53.23398+00:00
-- url     : https://prove2.me/theorems/b28e682c-f21d-423e-a263-34bec6191353
-- title:
--   Proposition 2.1, p. 7 — SOL(A,b,σ,p,1) is finite for each 0 < p < 1, and so is ⋃_{0<p<1} SOL(A,b,σ,p,1)
-- statement:
--   Assume the blanket assumptions of the paper for $q=1$: $\sigma\ge 0$, $\mathrm{FEA}(A,b,\sigma,1)\ne\emptyset$ and $\|b\|_1>\sigma$. Then
--
--   1. for every $0<p<1$ the optimal solution set $\mathrm{SOL}(A,b,\sigma,p,1)$ of problem (1.4), $\min\|x\|_p^p$ s.t. $\|Ax-b\|_1\le\sigma$, is a finite set; and
--   2. the union over all exponents in $(0,1)$ is a finite set:
--   $$\bigcup_{0<p<1}\mathrm{SOL}(A,b,\sigma,p,1)\ \text{ is finite.}$$
--
--   No condition on $A$ is required. The second clause is the compactness substitute in the proof of Theorem 2.2: along any sequence $p_k\downarrow 0$, optimal solutions can take only finitely many values.
--
--   Differences from the source: none.
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 7, Proposition 2.1

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP
theorem proposition_2_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b) :
    (∀ p ∈ Set.Ioo (0 : ℝ) 1, (SOL A b σ p 1).Finite) ∧
      (⋃ p ∈ Set.Ioo (0 : ℝ) 1, SOL A b σ p 1).Finite := by sorry
end SparseLpLq.SmallP
