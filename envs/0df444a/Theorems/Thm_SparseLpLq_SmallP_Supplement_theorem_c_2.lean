-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_Supplement_theorem_c_2
-- name    : SparseLpLq.SmallP.Supplement.theorem_c_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:15:55.92677+00:00
-- url     : https://prove2.me/theorems/1fda6b25-80e9-42e4-a6cc-859c6a7b5d1b
-- title:
--   Theorem C.2 — a global minimizer of (1.4) is, for every ϵ > 0, an ϵ-minimizer of F_λ for all λ ≥ some λ*_ϵ > 0
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, and the blanket assumptions of the paper (p. 1) hold for $q=1$: $\sigma\ge 0$, $\mathrm{FEA}(A,b,\sigma,1)=\{x:\|Ax-b\|_1\le\sigma\}\neq\emptyset$ and $\|b\|_1>\sigma$. Let $0<p<1$ and $F_\lambda(x)=\|x\|_p^p+\lambda(\|Ax-b\|_1-\sigma)_+$ (3.3).
--
--   Suppose $x^*$ is a global minimizer of (1.4), i.e. $x^*\in\mathrm{SOL}(A,b,\sigma,p,1)$. Then for every $\epsilon>0$ there exists $\lambda^*_\epsilon>0$ such that for every $\lambda\ge\lambda^*_\epsilon$, $x^*$ is an $\epsilon$-minimizer of (3.3) (Definition C.1(ii)):
--   $$F_\lambda(x^*)\ \le\ \min_{x\in\mathbb R^n}F_\lambda(x)+\epsilon .$$
--
--   So the penalty problem with a large enough finite parameter recovers the constrained optimum up to any prescribed accuracy.
--
--   **Formalization Note** "$\le\min_x F_\lambda(x)+\epsilon$" is written as $F_\lambda(x^*)\le F_\lambda(y)+\epsilon$ for every $y$, which avoids presupposing that the minimum is attained.
--
--   Differences from the source:
--   - encoding: F_λ(x_ϵ) ≤ min_x F_λ(x) + ϵ (Definition C.1(ii)) → ∀ y, F_λ(x) ≤ F_λ(y) + ϵ; reason: equivalent whenever the minimum exists (it does: F_λ is continuous and level-bounded) and does not presuppose it
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 26, Theorem C.2 and Definition C.1; proof pp. 26–27

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Penalty

open scoped ENNReal Matrix Topology

namespace SparseLpLq.SmallP.Supplement
open SparseLpLq.SmallP
theorem theorem_c_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → ℝ) (hx : x ∈ SOL A b σ p 1) :
    ∀ ε : ℝ, 0 < ε → ∃ lamε : ℝ, 0 < lamε ∧
      ∀ lam : ℝ, lamε ≤ lam → IsEpsMinPen A b σ p lam ε x := by sorry
end SparseLpLq.SmallP.Supplement
