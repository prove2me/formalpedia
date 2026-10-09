-- Prove2me | Theorems.Thm_TensorBTD_Gramian_diagonal_blocks
-- name    : TensorBTD.Gramian.diagonal_blocks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:06.301424+00:00
-- url     : https://prove2.me/theorems/4bad248b-228b-4d72-bb79-c56129f60e57
-- title:
--   Proof of Theorem 4.5, p. 12 — diagonal blocks: ⟨∂ℱ/∂a^(n)_{i r1}, ∂ℱ/∂a^(n)_{j r2}⟩ = w^{n}_{r1r2} δ_ij
-- statement:
--   In the setting of the unstructured CPD in $R'$ rank-one terms, with factor matrices $A^{(1)},\dots,A^{(N)}$ and residual $\mathcal F$, let $W^{\{n\}} = \ast_{m\ne n} A^{(m)\mathrm H}A^{(m)}$ be the Hadamard product of the Gramians of all factor matrices except the $n$-th, with entries $w^{\{n\}}_{r_1r_2}$. Then for every mode $n$, columns $r_1,r_2$ and rows $i,j$ of mode $n$:
--
--   1. the tensor inner product (Definition 2.1, conjugate on the first argument) of two partial derivatives with respect to entries of the same factor matrix is
--   $$\left\langle \frac{\partial\mathcal F}{\partial a^{(n)}_{ir_1}},\ \frac{\partial\mathcal F}{\partial a^{(n)}_{jr_2}}\right\rangle = \begin{cases} w^{\{n\}}_{r_1r_2} & i=j,\\ 0 & \text{otherwise;}\end{cases}$$
--   2. consequently the $I_n\times I_n$ block of the Gramian $J^{\mathrm H}J$ of the CPD Jacobian $J = \partial\,\mathrm{vec}(\mathcal F)/\partial x^{\mathrm T}$ at rows belonging to column $a^{(n)}_{r_1}$ and columns belonging to $a^{(n)}_{r_2}$ is
--   $$\left(\frac{\partial\,\mathrm{vec}(\mathcal F)}{\partial a^{(n)\mathrm T}_{r_1}}\right)^{\mathrm H}\left(\frac{\partial\,\mathrm{vec}(\mathcal F)}{\partial a^{(n)\mathrm T}_{r_2}}\right) = w^{\{n\}}_{r_1r_2}\,\mathbb I_{I_n}.$$
--
--   These are the diagonal blocks $\Pi^{(n,n)} = W^{\{n\}}\otimes\mathbb I_{I_n}$ of (4.12). The statement holds for every tensor and every choice of factor matrices.
--
--   **Formalization Note.** Indices are 0-based; the Jacobian is the complex Jacobian of the unstructured CPD residual of the mission's setting, and the block is extracted from $J^{\mathrm H}J$ at the unknowns $(n,(r_1,i))$ and $(n,(r_2,j))$.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 12, proof of Theorem 4.5, "Diagonal blocks" displays

import Mathlib
import Definitions.Def_TensorBTD_Gramian_Setting

namespace TensorBTD.Gramian

open Matrix

theorem diagonal_blocks {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) (r1 r2 : Col L) :
    (∀ i j : Fin (I n),
      tensorInner (fun ι => jac (cpdResidual T) x ι ⟨n, (r1, i)⟩)
          (fun ι => jac (cpdResidual T) x ι ⟨n, (r2, j)⟩) =
        if i = j then W {n} (cpdFactor x) r1 r2 else 0) ∧
    (Matrix.of fun i j : Fin (I n) =>
        ((jac (cpdResidual T) x)ᴴ * jac (cpdResidual T) x) ⟨n, (r1, i)⟩ ⟨n, (r2, j)⟩) =
      W {n} (cpdFactor x) r1 r2 • (1 : Matrix (Fin (I n)) (Fin (I n)) ℂ) := by sorry

end TensorBTD.Gramian
