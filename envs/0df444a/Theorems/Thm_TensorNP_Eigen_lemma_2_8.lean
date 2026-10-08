-- Prove2me | Theorems.Thm_TensorNP_Eigen_lemma_2_8
-- name    : TensorNP.Eigen.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:26.48469+00:00
-- url     : https://prove2.me/theorems/f336b545-15d6-46d9-bdbc-d0faad91fd7b
-- title:
--   Lemma 2.8 — padding a real quadratic system to $r\ge m+1$ equations in $s\ge n$ unknowns
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb R^{n\times n}$ and $G_i(\mathbf x)=\mathbf x^\top A_i\mathbf x$. Let $r\ge m+1$ and $s\ge n$, and define the $r$ matrices of size $s\times s$
--
--   $$B_i=\begin{bmatrix}A_i&0\\0&0\end{bmatrix}\ (i=1,\dots,m),\qquad B_j=\begin{bmatrix}0&0\\0&0\end{bmatrix}\ (j=m+1,\dots,r-1),\qquad B_r=\begin{bmatrix}0&0\\0&I\end{bmatrix},$$
--
--   where $I$ is the $(s-n)\times(s-n)$ identity matrix, and $H_i(\mathbf x)=\mathbf x^\top B_i\mathbf x$. Then $\{H_i(\mathbf x)=0\}_{i=1}^{r}$ has a nonzero solution $\mathbf x\in\mathbb R^s$ if and only if $\{G_i(\mathbf x)=0\}_{i=1}^{m}$ has a nonzero solution $\mathbf x\in\mathbb R^n$.
--
--   The lemma lets a quadratic system be made square, the shape of the eigenvalue equations of a tensor.
--
--   **Formalization Note** The case $s=n$ is included, where $B_r=0$. Indices are 0-based, so $B_r$ is matrix number $r-1$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:14, Lemma 2.8

import Mathlib
import Definitions.Def_TensorNP_Eigen_Construction

namespace TensorNP.Eigen

open Matrix

/-- Lemma 2.8: for `A_1, …, A_m ∈ ℝ^{n×n}`, `r ≥ m + 1` and `s ≥ n`, the padded system
`xᵀ B_i x = 0` (`i = 1, …, r`) with `B_i = [A_i 0; 0 0]`, `B_j = 0` (`m < j < r`),
`B_r = [0 0; 0 I]` has a nonzero solution `x ∈ ℝ^s` if and only if `{xᵀ A_i x = 0}_{i=1}^m` has
a nonzero solution `x ∈ ℝ^n`. -/
theorem lemma_2_8 {m n r s : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hr : m + 1 ≤ r)
    (hs : n ≤ s) :
    QuadSolvable (padSystem A r s) ↔ QuadSolvable A := by sorry

end TensorNP.Eigen
