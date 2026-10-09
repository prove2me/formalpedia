-- Prove2me | Theorems.Thm_TensorBTD_Gramian_theorem_4_5
-- name    : TensorBTD.Gramian.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:18.269699+00:00
-- url     : https://prove2.me/theorems/73b1ac0c-b898-430c-9d14-e95d0d2adc81
-- title:
--   Theorem 4.5, p. 12 — JᴴJ = Σ·[Π^(n1,n2)]·Σᵀ with Π^(n,n) = W^{n} ⊗ 𝕀 and rank-one off-diagonal blocks
-- statement:
--   Let $\mathcal T\in\mathbb C^{I_1\times\cdots\times I_N}$, $N = P+Q$, and consider the (rank-$L_r\circ$ rank-1) block term decomposition read as a structured CPD in $R' = \sum_r L_r$ rank-one terms, with unknowns $z = (\mathrm{vec}A^{(1)},\dots,\mathrm{vec}A^{(P)},\mathrm{vec}C^{(1)},\dots,\mathrm{vec}C^{(Q)})$ and factor matrices $A^{(p)}$ ($p\le P$) and $A^{(P+q)} = C^{(q)}E$ (3.6). Let $J = \partial\,\mathrm{vec}(\mathcal F_{\mathrm{BTD}})/\partial z^{\mathrm T}$ be the complex Jacobian of the residual, and let $F^{(q)} = E\otimes\mathbb I_{I_{P+q}}$. For mode sets $\sigma$ write $W^\sigma = \ast_{m\notin\sigma}A^{(m)\mathrm H}A^{(m)}$, with entries $w^\sigma_{r_1r_2}$. Then the Gramian $J^{\mathrm H}J$ is given by
--   $$J^{\mathrm H}J = \Sigma\cdot\begin{bmatrix}\Pi^{(1,1)}&\cdots&\Pi^{(1,N)}\\ \vdots&\ddots&\vdots\\ \Pi^{(N,1)}&\cdots&\Pi^{(N,N)}\end{bmatrix}\cdot\Sigma^{\mathrm T},\qquad \Sigma = \mathrm{diag}(\mathbb I_{I_1R'},\dots,\mathbb I_{I_PR'},F^{(1)},\dots,F^{(Q)}),$$
--   where
--   $$\Pi^{(n_1,n_2)} = \left(\frac{\partial\,\mathrm{vec}(\mathcal F_{\mathrm{BTD}})}{\partial\,\mathrm{vec}(A^{(n_1)})^{\mathrm T}}\right)^{\mathrm H}\left(\frac{\partial\,\mathrm{vec}(\mathcal F_{\mathrm{BTD}})}{\partial\,\mathrm{vec}(A^{(n_2)})^{\mathrm T}}\right) = \begin{cases} W^{\{n\}}\otimes\mathbb I_{I_n} & n = n_1 = n_2,\\[2pt] \Big[\,w^{\{n_1,n_2\}}_{r_1r_2}\, a^{(n_1)}_{r_2}\,a^{(n_2)\mathrm H}_{r_1}\Big]_{r_1,r_2=1}^{R'} & \text{otherwise.}\end{cases}$$
--   The derivatives in $\Pi^{(n_1,n_2)}$ are taken with all $N$ factor matrices treated as free (the unstructured CPD in $R'$ terms) and evaluated at the factor matrices of $z$. The theorem therefore asserts two things, both for every tensor and every $z$:
--
--   1. the Gramian of the unstructured CPD Jacobian equals the explicit block matrix $\Pi$ of (4.12);
--   2. $J^{\mathrm H}J = \Sigma\,\Pi\,\Sigma^{\mathrm T}$ (4.10).
--
--   The result makes $J^{\mathrm H}J$ storable as the factor matrices and their Gramians, which is the basis of the paper's matrix-free Gauss–Newton and Levenberg–Marquardt methods.
--
--   **Formalization Note.** Modes are `Fin P ⊕ Fin Q`, columns `Σ r, Fin (L r)`, all indices 0-based, and vec order is (column, row). $\Pi$ is the mission's `PiMat`, whose diagonal blocks are written entrywise as $w^{\{n\}}_{r_1r_2}\delta_{ij}$. Since $A^{(P+q)}$ is not an unknown of the BTD, the derivative with respect to $\mathrm{vec}(A^{(n)})$ in (4.12) is that of the unstructured CPD residual at the point whose factor matrices are those of $z$; this is how the paper's proof reads it. The paper's standing assumption $P, Q\ge 1$ and the qualifiers "nonzero" and "rank-$L_r$" are dropped: the identity holds for all sizes and all factor matrices (Q = 0 gives the plain CPD in $R'$ terms).
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 12, Theorem 4.5, (4.10)–(4.12); proof pp. 12–13

import Mathlib
import Definitions.Def_TensorBTD_Gramian_Setting

namespace TensorBTD.Gramian

open Matrix

theorem theorem_4_5 {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (z : Unk I L → ℂ) :
    (jac (cpdResidual T) (fullVec z))ᴴ * jac (cpdResidual T) (fullVec z) = PiMat (factor z) ∧
    (jac (residual T) z)ᴴ * jac (residual T) z =
      Sigma I L * PiMat (factor z) * (Sigma I L)ᵀ := by sorry

end TensorBTD.Gramian
