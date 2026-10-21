-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_lemma_C1
-- name    : ShapleySnowSG.Kernel.lemma_C1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:02.233007+00:00
-- url     : https://prove2.me/theorems/694be321-f706-4577-97ca-3b9947d6089c
-- title:
--   Lemma C1, p. 30 — det(A + vB) = 0 and ᵗx B y ≠ 0 for kernel vectors x, y force a rank drop of A + wB at w = v
-- statement:
--   Let $A,B$ be real square matrices of the same size and $v\in\mathbb R$ with $\det(A+vB)=0$. Suppose there are $x\in\mathrm{Ker}({}^t(A+vB))$ and $y\in\mathrm{Ker}(A+vB)$ with ${}^tx\,B\,y\neq0$. Then
--   $$\mathrm{rank}(A+vB)<\max_{w\in\mathbb R}\mathrm{rank}(A+wB).$$
--
--   This is the criterion, due to Muhič and Plestenjak, by which a common root of a singular pencil is detected through its rank.
--
--   **Formalization Note** "$<\max_w$" is encoded as the existence of a real $w$ with strictly larger rank.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 30, Lemma C1

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Lemma C1, p. 30: let `A`, `B` be square of the same size and `det(A + vB) = 0`. If some
`x ∈ Ker(ᵗ(A + vB))` and `y ∈ Ker(A + vB)` have `ᵗx B y ≠ 0`, then
`rank(A + vB) < max_{w ∈ ℝ} rank(A + wB)`. -/
theorem lemma_C1 {m : Type*} [Fintype m] [DecidableEq m] (A B : Matrix m m ℝ) (v : ℝ)
    (hdet : (A + v • B).det = 0) (x y : m → ℝ) (hx : (A + v • B)ᵀ *ᵥ x = 0)
    (hy : (A + v • B) *ᵥ y = 0) (hxy : x ⬝ᵥ (B *ᵥ y) ≠ 0) :
    ∃ w : ℝ, (A + v • B).rank < (A + w • B).rank := by sorry

end ShapleySnowSG.Kernel
