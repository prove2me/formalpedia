-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_lemma_4_4
-- name    : QuadMatIneq.Stabilization.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:39.272704+00:00
-- url     : https://prove2.me/theorems/a70ef714-0113-4e34-a7ea-3c96f5b0eea5
-- title:
--   Lemma 4.4 — for S ⩾ 0 and x ≠ 0 there is X̄ ∈ ℝ^{n×(n−1)} with xᵀSX̄ = 0 and [x X̄] nonsingular
-- statement:
--   Let $S\in\mathbb{S}^n$ with $S\geqslant 0$, and let $x\in\mathbb{R}^n$ be nonzero. Then there exists $\bar X\in\mathbb{R}^{n\times(n-1)}$ such that
--   $$x^\top S\bar X=0 \qquad\text{and}\qquad \begin{bmatrix}x&\bar X\end{bmatrix}\ \text{is nonsingular}.$$
--
--   This completion lemma is the linear-algebra step behind Lemma 4.5: it extends a single vector $x$ to a basis whose remaining vectors are $S$-orthogonal to $x$.
--
--   **Formalization Note** Since $x\neq 0$ forces $n\geqslant 1$, the dimension is written $n=k+1$ and $\bar X$ has $k$ columns, avoiding natural-number subtraction. $[x\ \bar X]$ is the $n\times n$ matrix whose first column is $x$ and whose remaining columns are those of $\bar X$; nonsingular is `IsUnit`. $x^\top S\bar X$ is the row vector `(x ᵥ* S) ᵥ* Xb`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Lemma 4.4, p. 10

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Lemma 4.4, p. 10, with `n = k + 1` (a nonzero `x ∈ ℝⁿ` forces `n ⩾ 1`). The matrix
`[x X̄]` has first column `x` and remaining columns those of `X̄`. -/
theorem lemma_4_4 {k : ℕ} (S : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (hS : S.PosSemidef)
    (x : Fin (k + 1) → ℝ) (hx : x ≠ 0) :
    ∃ Xb : Matrix (Fin (k + 1)) (Fin k) ℝ,
      (x ᵥ* S) ᵥ* Xb = 0 ∧
        IsUnit (Matrix.of fun i : Fin (k + 1) => (Fin.cons (x i) (Xb i) : Fin (k + 1) → ℝ)) := by sorry

end QuadMatIneq.Stabilization
