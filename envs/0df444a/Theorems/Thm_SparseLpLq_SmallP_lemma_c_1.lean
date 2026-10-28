-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_lemma_c_1
-- name    : SparseLpLq.SmallP.lemma_c_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:46:07.680303+00:00
-- url     : https://prove2.me/theorems/f4839e07-fb14-45da-a04f-50314b7b9cff
-- title:
--   Lemma C.1, p. 24 — FEA(A,b,σ,1) = {x : UAx ≤ Ub + σ1}, U the matrix of all sign vectors
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\sigma\ge 0$. Let $\mathcal U=\{u_1,\dots,u_{2^m}\}=\{-1,1\}^m$ be the set of all sign vectors and $U=[u_1,\dots,u_{2^m}]^\top\in\mathbb R^{2^m\times m}$ the matrix whose rows are these vectors, as in (C.1). Then the $\ell_1$-feasible set is a polyhedron described by $2^m$ linear inequalities:
--
--   $$\mathrm{FEA}(A,b,\sigma,1)=\{x\in\mathbb R^n : \|Ax-b\|_1\le\sigma\}=\{x\in\mathbb R^n : UAx\le Ub+\sigma\mathbf 1\},$$
--
--   where $\mathbf 1=(1,\dots,1)^\top\in\mathbb R^{2^m}$. Row by row, the right-hand side is the set of $x$ with $u^\top Ax\le u^\top b+\sigma$ for every $u\in\{-1,1\}^m$.
--
--   The lemma is what makes $\mathrm{FEA}(A,b,\sigma,1)$ a convex polyhedron, so that its intersection with each orthant has finitely many extreme points; this finiteness underlies Proposition 2.1 and Theorem 2.2.
--
--   **Formalization Note** The rows of $U$ are quantified directly as all vectors $u$ with every entry equal to $1$ or $-1$, instead of an enumerated $2^m\times m$ matrix.
--
--   Differences from the source:
--   - generalization: σ > 0 → 0 ≤ σ; reason: the identity holds verbatim at σ = 0 (both sides are {x : Ax = b}), and the paper's blanket assumption and Theorem 2.2 allow σ = 0; every instance with σ > 0 is an instance of the Lean statement
--   - encoding: the matrix U = [u₁, …, u_{2^m}]ᵀ and the vector inequality UAx ≤ Ub + σ1 → ∀ u with every uᵢ ∈ {1, −1}, u ⬝ᵥ (A x) ≤ u ⬝ᵥ b + σ; reason: the rows of U are exactly the sign vectors, and a vector inequality is the conjunction of its rows
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 24, Lemma C.1 and (C.1)

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP
theorem lemma_c_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) :
    FEA A b σ 1 =
      {x | ∀ u : Fin m → ℝ, (∀ i, u i = 1 ∨ u i = -1) → u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b + σ} := by sorry
end SparseLpLq.SmallP
