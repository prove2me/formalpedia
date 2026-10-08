-- Prove2me | Theorems.Thm_TensorNP_Eigen_lemma_2_7
-- name    : TensorNP.Eigen.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:09.524326+00:00
-- url     : https://prove2.me/theorems/7165a98c-dfe6-4224-af56-f707ccc2d39c
-- title:
--   Lemma 2.7 — $2m$ real quadratic equations in $2n$ unknowns encode $m$ complex ones in $n$ unknowns
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb Q^{n\times n}$ (not necessarily symmetric) and $G_i(\mathbf z)=\mathbf z^\top A_i\mathbf z$. Define the $2m$ matrices of size $2n\times 2n$
--
--   $$B_i=\begin{bmatrix}A_i&0\\0&-A_i\end{bmatrix},\qquad B_{m+i}=\begin{bmatrix}0&A_i\\A_i&0\end{bmatrix},\qquad i=1,\dots,m,$$
--
--   and $H_j(\mathbf x)=\mathbf x^\top B_j\mathbf x$. Then the equations $\{H_j(\mathbf x)=0\}_{j=1}^{2m}$ have a nonzero real solution $\mathbf x\in\mathbb R^{2n}$ if and only if the equations $\{G_i(\mathbf z)=0\}_{i=1}^{m}$ have a nonzero complex solution $\mathbf z\in\mathbb C^n$.
--
--   The lemma transfers complex feasibility of a quadratic system to real feasibility of a system twice the size, which is how the reduction reaches the real numbers.
--
--   **Formalization Note** The matrices are rational, as in Problem 2.2, and are cast to $\mathbb R$ and to $\mathbb C$. The unknowns $\mathbf x=[\mathbf u^\top,\mathbf v^\top]^\top$ list $\mathbf u$ first, and the equations list $B_1,\dots,B_m$ first.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:14, Lemma 2.7

import Mathlib
import Definitions.Def_TensorNP_Eigen_Construction

namespace TensorNP.Eigen

open Matrix

/-- Lemma 2.7: for rational `A_1, …, A_m ∈ ℚ^{n×n}`, the `2m` real equations `xᵀ B_j x = 0` with
`B_i = [A_i 0; 0 −A_i]`, `B_{m+i} = [0 A_i; A_i 0]` have a nonzero real solution `x ∈ ℝ^{2n}`
if and only if the equations `zᵀ A_i z = 0` have a nonzero complex solution `z ∈ ℂ^n`. -/
theorem lemma_2_7 {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ) :
    QuadSolvable (castMatrices ℝ (realSplit A)) ↔ QuadSolvable (castMatrices ℂ A) := by sorry

end TensorNP.Eigen
