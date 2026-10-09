-- Prove2me | Theorems.Thm_TensorBTD_Gramian_blocks_via_sigma
-- name    : TensorBTD.Gramian.blocks_via_sigma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:14.874969+00:00
-- url     : https://prove2.me/theorems/e0bd70a6-7e04-48fe-9729-4c51b40bc750
-- title:
--   Proof of Theorem 4.5, pp. 12–13 — the blocks of JᴴJ involving C^(q) are Π·F^(q)ᵀ, F^(q)·Π and F^(q1)·Π·F^(q2)ᵀ
-- statement:
--   Let $J = \partial\,\mathrm{vec}(\mathcal F_{\mathrm{BTD}})/\partial z^{\mathrm T}$ be the Jacobian of the (rank-$L_r\circ$ rank-1) BTD residual with respect to its unknowns $z$, and let $J_{\mathrm{CPD}}$ be the Jacobian of the unstructured CPD residual in $R'$ terms (all factor matrices $A^{(1)},\dots,A^{(N)}$ free), evaluated at the factor matrices of $z$, so that $A^{(P+q)} = C^{(q)}E$. Write
--   $$\Pi^{(n_1,n_2)} = \left(\frac{\partial\,\mathrm{vec}(\mathcal F)}{\partial\,\mathrm{vec}(A^{(n_1)})^{\mathrm T}}\right)^{\mathrm H}\left(\frac{\partial\,\mathrm{vec}(\mathcal F)}{\partial\,\mathrm{vec}(A^{(n_2)})^{\mathrm T}}\right)$$
--   for the blocks of $J_{\mathrm{CPD}}^{\mathrm H}J_{\mathrm{CPD}}$, and $\Sigma = \mathrm{diag}(\mathbb I_{I_1R'},\dots,\mathbb I_{I_PR'},F^{(1)},\dots,F^{(Q)})$ with $F^{(q)} = E\otimes\mathbb I_{I_{P+q}}$. Then for every tensor $\mathcal T$ and every $z$,
--   $$J^{\mathrm H}J = \Sigma\cdot\left(J_{\mathrm{CPD}}^{\mathrm H}J_{\mathrm{CPD}}\right)\cdot\Sigma^{\mathrm T}.$$
--   Block by block this says: the $(p_1,p_2)$ block of $J^{\mathrm H}J$ is $\Pi^{(p_1,p_2)}$; the $(p,P+q)$ block is $\Pi^{(p,P+q)}F^{(q)\mathrm T}$; the $(P+q,p)$ block is $F^{(q)}\Pi^{(P+q,p)}$; and the $(P+q_1,P+q_2)$ block is $F^{(q_1)}\Pi^{(P+q_1,P+q_2)}F^{(q_2)\mathrm T}$.
--
--   **Formalization Note.** The paper prints the $(P+q,p)$ block as $F^{(q)}\cdot\Pi^{(p,P+q)}$, a misprint for $F^{(q)}\cdot\Pi^{(P+q,p)}$ (the printed product does not even have matching dimensions unless $I_p = I_{P+q}$); the Lean states the correct identity, in assembled matrix form. $\Sigma$ has rows indexed by the unknowns $z$ and columns by the unknowns of the unstructured CPD; it is real, so $\Sigma^{\mathrm T} = \Sigma^{\mathrm H}$.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), pp. 12–13, proof of Theorem 4.5, closing paragraph

import Mathlib
import Definitions.Def_TensorBTD_Gramian_Setting

namespace TensorBTD.Gramian

open Matrix

theorem blocks_via_sigma {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (z : Unk I L → ℂ) :
    (jac (residual T) z)ᴴ * jac (residual T) z =
      Sigma I L * ((jac (cpdResidual T) (fullVec z))ᴴ * jac (cpdResidual T) (fullVec z)) *
        (Sigma I L)ᵀ := by sorry

end TensorBTD.Gramian
