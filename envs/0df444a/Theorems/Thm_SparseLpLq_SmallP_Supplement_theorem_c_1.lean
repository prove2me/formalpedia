-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_Supplement_theorem_c_1
-- name    : SparseLpLq.SmallP.Supplement.theorem_c_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:15:23.372954+00:00
-- url     : https://prove2.me/theorems/86026705-088e-4779-916a-57ba16deb002
-- title:
--   Theorem C.1 — a local minimizer of (1.4) is a local minimizer of F_λ for every λ ≥ some λ* > 0
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, and the blanket assumptions of the paper (p. 1) hold for $q=1$: $\sigma\ge 0$, $\mathrm{FEA}(A,b,\sigma,1)=\{x:\|Ax-b\|_1\le\sigma\}\neq\emptyset$ and $\|b\|_1>\sigma$. Let $0<p<1$ and $F_\lambda(x)=\|x\|_p^p+\lambda(\|Ax-b\|_1-\sigma)_+$ be the penalty function (3.3).
--
--   Suppose $x^*$ is a local minimizer of (1.4): $x^*\in\mathrm{FEA}(A,b,\sigma,1)$ and $\|x^*\|_p^p\le\|x\|_p^p$ for all feasible $x$ in a neighbourhood of $x^*$. Then there exists $\lambda^*>0$ such that for every $\lambda\ge\lambda^*$,
--   $$F_\lambda(x^*)\le F_\lambda(x)\quad\text{for all }x\text{ in a neighbourhood of }x^*,$$
--   that is, $x^*$ is a local minimizer of (3.3).
--
--   This is the exact penalty property of (3.3) for local minimizers: a single finite penalty parameter, and every larger one, preserves local optimality.
--
--   Differences from the source: none.
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 25, Theorem C.1; proof pp. 25–26

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Penalty

open scoped ENNReal Matrix Topology

namespace SparseLpLq.SmallP.Supplement
open SparseLpLq.SmallP
theorem theorem_c_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → ℝ) (hx : IsLocalMin14 A b σ p x) :
    ∃ lamStar : ℝ, 0 < lamStar ∧ ∀ lam : ℝ, lamStar ≤ lam → IsLocalMinPen A b σ p lam x := by sorry
end SparseLpLq.SmallP.Supplement
