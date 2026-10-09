-- Prove2me | Theorems.Thm_TensorBTD_Gramian_proposition_4_1
-- name    : TensorBTD.Gramian.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:18.543105+00:00
-- url     : https://prove2.me/theorems/dd8a6193-7ab0-4f7a-a2b8-6bd07276fa76
-- title:
--   Proposition 4.1, p. 7 — vec(C^(q)E)ᵀ = vec(C^(q))ᵀF^(q) and ∂/∂vec(C^(q))ᵀ = ∂/∂vec(A^(P+q))ᵀ·F^(q)ᵀ
-- statement:
--   Let $E\in\mathbb R^{R\times R'}$ be the block diagonal matrix $\mathrm{diag}(1_{1\times L_1},\dots,1_{1\times L_R})$ and $F^{(q)} = E\otimes\mathbb I_{I_{P+q}}$. Then:
--
--   1. for every $C\in\mathbb C^{I_{P+q}\times R}$,
--   $$\mathrm{vec}(C\cdot E)^{\mathrm T} = \mathrm{vec}(C)^{\mathrm T}\cdot F^{(q)};$$
--   2. (chain rule (4.3b)) for every tensor $\mathcal T$ and every vector of unknowns $z = (\mathrm{vec}A^{(1)},\dots,\mathrm{vec}A^{(P)},\mathrm{vec}C^{(1)},\dots,\mathrm{vec}C^{(Q)})$ of the (rank-$L_r\circ$ rank-1) BTD, the columns of the BTD Jacobian $J = \partial\,\mathrm{vec}(\mathcal F_{\mathrm{BTD}})/\partial z^{\mathrm T}$ that belong to $\mathrm{vec}(C^{(q)})$ are
--   $$\frac{\partial\,\mathrm{vec}(\mathcal F_{\mathrm{BTD}})}{\partial\,\mathrm{vec}(C^{(q)})^{\mathrm T}} = \frac{\partial\,\mathrm{vec}(\mathcal F_{\mathrm{BTD}})}{\partial\,\mathrm{vec}(A^{(P+q)})^{\mathrm T}}\cdot F^{(q)\mathrm T},$$
--   where the right-hand Jacobian is that of the unstructured CPD residual (all $N$ factor matrices free) evaluated at the factor matrices of $z$, i.e. with $A^{(P+q)} = C^{(q)}E$.
--
--   The proposition lets one ignore the structure $A^{(P+q)} = C^{(q)}E$ when differentiating, and then correct by the fixed matrix $F^{(q)}$.
--
--   **Formalization Note.** Part (4.3a) of the proposition (the matrix form $\partial/\partial C^{(q)} = \partial/\partial A^{(P+q)}\cdot E^{\mathrm T}$ of the cogradient) is not formalized here; this mission formalizes the vec identity and the Jacobian form (4.3b), which is what Theorem 4.5 uses. Row vectors times matrices are Mathlib's `vecMul`; `vec` is column-major, indexed by (column, row). The left-hand side of part 2 is the submatrix of $J$ at the columns $(q,(r,i))$, the right-hand side the submatrix of the unstructured CPD Jacobian at the columns $(P+q,((r,l),i))$, times $F^{(q)\mathrm T}$. Since $A^{(P+q)}$ is not an unknown of the BTD, $\partial/\partial A^{(P+q)}$ is read as the derivative of the unstructured CPD residual, as in the proof of Theorem 4.5.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 7, Proposition 4.1 (vec identity and (4.3b))

import Mathlib
import Definitions.Def_TensorBTD_Gramian_Setting

namespace TensorBTD.Gramian

open Matrix

theorem proposition_4_1 {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (q : Fin Q) :
    (∀ C : Matrix (Fin (I (.inr q))) (Fin R) ℂ,
      Matrix.vec (C * E L) = Matrix.vecMul (Matrix.vec C) (F I L q)) ∧
    (∀ (T : Tensor I) (z : Unk I L → ℂ),
      (jac (residual T) z).submatrix id
          (fun y : Fin R × Fin (I (.inr q)) => (⟨.inr q, y⟩ : Unk I L)) =
        (jac (cpdResidual T) (fullVec z)).submatrix id
            (fun y : Col L × Fin (I (.inr q)) => (⟨.inr q, y⟩ : GIdx I L)) *
          (F I L q)ᵀ) := by sorry

end TensorBTD.Gramian
