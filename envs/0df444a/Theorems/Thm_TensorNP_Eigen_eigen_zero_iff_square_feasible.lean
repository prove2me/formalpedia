-- Prove2me | Theorems.Thm_TensorNP_Eigen_eigen_zero_iff_square_feasible
-- name    : TensorNP.Eigen.eigen_zero_iff_square_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:08.495975+00:00
-- url     : https://prove2.me/theorems/e07f4459-ea31-4233-ba13-1afd04e68c21
-- title:
--   Proof of Theorem 1.3 — $0$ is a real eigenvalue of $\mathcal A$ iff a square quadratic system is feasible
-- statement:
--   Let $\mathcal A=[\![a_{ijk}]\!]\in\mathbb Q^{n\times n\times n}$ and, for $k=1,\dots,n$, let $A_k\in\mathbb Q^{n\times n}$ be its slice $A_k(i,j)=a_{ijk}$. Then $0$ is an eigenvalue of $\mathcal A$ over $\mathbb R$, i.e. there is $\mathbf 0\ne\mathbf x\in\mathbb R^n$ with $\sum_{i,j}a_{ijk}x_ix_j=0$ for all $k$, if and only if the square system
--
--   $$\mathbf x^\top A_k\mathbf x=0,\qquad k=1,\dots,n,$$
--
--   of $n$ quadratic equations in $n$ unknowns has a nonzero real solution.
--
--   This identifies tensor $0$-eigenvalue with square quadratic feasibility ($m=n$ in Problem 2.2), the first step of the paper's proof of Theorem 1.3.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:20, proof of Theorem 1.3

import Mathlib
import Definitions.Def_TensorNP_Eigen_Defs

namespace TensorNP.Eigen

open Matrix

/-- Proof of Theorem 1.3, first sentence: `0` is a real eigenvalue of `A ∈ ℚ^{n×n×n}` if and only
if the square system `xᵀ A_k x = 0` (`k = 1, …, n`) with `A_k(i, j) = a_{ijk}` has a nonzero
real solution. -/
theorem eigen_zero_iff_square_feasible {n : ℕ} (A : Fin n → Fin n → Fin n → ℚ) :
    IsEigenvalue (castTensor ℝ A) 0 ↔
      QuadSolvable (castMatrices ℝ (fun k : Fin n => Matrix.of fun i j => A i j k)) := by sorry

end TensorNP.Eigen
