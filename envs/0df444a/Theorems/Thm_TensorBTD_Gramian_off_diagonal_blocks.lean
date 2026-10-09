-- Prove2me | Theorems.Thm_TensorBTD_Gramian_off_diagonal_blocks
-- name    : TensorBTD.Gramian.off_diagonal_blocks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:04.014993+00:00
-- url     : https://prove2.me/theorems/6e8abc18-6079-4979-b164-ae1f48959c62
-- title:
--   Proof of Theorem 4.5, p. 12 — off-diagonal blocks: ⟨∂ℱ/∂a^(n1)_{i r1}, ∂ℱ/∂a^(n2)_{j r2}⟩ = w^{n1,n2}_{r1r2} a^(n1)_{i r2} ā^(n2)_{j r1}
-- statement:
--   In the setting of the unstructured CPD in $R'$ rank-one terms, with factor matrices $A^{(1)},\dots,A^{(N)}$ and residual $\mathcal F$, let $W^{\{n_1,n_2\}} = \ast_{m\notin\{n_1,n_2\}} A^{(m)\mathrm H}A^{(m)}$, with entries $w^{\{n_1,n_2\}}_{r_1r_2}$. Then for every pair of distinct modes $n_1\ne n_2$, columns $r_1,r_2$, a row $i$ of mode $n_1$ and a row $j$ of mode $n_2$:
--
--   1. the tensor inner product (conjugate on the first argument) of the two partial derivatives is
--   $$\left\langle \frac{\partial\mathcal F}{\partial a^{(n_1)}_{ir_1}},\ \frac{\partial\mathcal F}{\partial a^{(n_2)}_{jr_2}}\right\rangle = w^{\{n_1,n_2\}}_{r_1r_2}\; a^{(n_1)}_{ir_2}\;\overline{a^{(n_2)}_{jr_1}};$$
--   2. consequently the $I_{n_1}\times I_{n_2}$ block of the Gramian $J^{\mathrm H}J$ of the CPD Jacobian, at rows belonging to column $a^{(n_1)}_{r_1}$ and columns belonging to $a^{(n_2)}_{r_2}$, is the rank-one matrix
--   $$\left(\frac{\partial\,\mathrm{vec}(\mathcal F)}{\partial a^{(n_1)\mathrm T}_{r_1}}\right)^{\mathrm H}\left(\frac{\partial\,\mathrm{vec}(\mathcal F)}{\partial a^{(n_2)\mathrm T}_{r_2}}\right) = w^{\{n_1,n_2\}}_{r_1r_2}\; a^{(n_1)}_{r_2}\,a^{(n_2)\mathrm H}_{r_1}.$$
--
--   Note the crossed column indices: the $(r_1,r_2)$ block involves column $r_2$ of $A^{(n_1)}$ and column $r_1$ of $A^{(n_2)}$. These are the off-diagonal blocks of (4.12). The statement holds for every tensor and every choice of factor matrices.
--
--   **Formalization Note.** Indices are 0-based. The rank-one matrix $u v^{\mathrm H}$ is written with Mathlib's `vecMulVec u (conj v)`.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 12, proof of Theorem 4.5, "Off-diagonal blocks" displays

import Mathlib
import Definitions.Def_TensorBTD_Gramian_Setting

namespace TensorBTD.Gramian

open Matrix

theorem off_diagonal_blocks {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (n1 n2 : Fin P ⊕ Fin Q) (hn : n1 ≠ n2) (r1 r2 : Col L) :
    (∀ (i : Fin (I n1)) (j : Fin (I n2)),
      tensorInner (fun ι => jac (cpdResidual T) x ι ⟨n1, (r1, i)⟩)
          (fun ι => jac (cpdResidual T) x ι ⟨n2, (r2, j)⟩) =
        W {n1, n2} (cpdFactor x) r1 r2 * cpdFactor x n1 i r2 *
          starRingEnd ℂ (cpdFactor x n2 j r1)) ∧
    (Matrix.of fun (i : Fin (I n1)) (j : Fin (I n2)) =>
        ((jac (cpdResidual T) x)ᴴ * jac (cpdResidual T) x) ⟨n1, (r1, i)⟩ ⟨n2, (r2, j)⟩) =
      W {n1, n2} (cpdFactor x) r1 r2 •
        Matrix.vecMulVec (fun i => cpdFactor x n1 i r2)
          (fun j => starRingEnd ℂ (cpdFactor x n2 j r1)) := by sorry

end TensorBTD.Gramian
