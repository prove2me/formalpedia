-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_proposition_4
-- name    : SunNLSDP.Equiv.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:34.620448+00:00
-- url     : https://prove2.me/theorems/f2d02fa6-7779-4149-8644-fdff5f60ef0f
-- title:
--   Proposition 4, p. 9 — structure (21) of ∂_BΠ_{S^p_+}(A) and ∂Π_{S^p_+}(A) through ∂_BΠ_{S^{|β|}_+}(0), ∂Π_{S^{|β|}_+}(0)
-- statement:
--   Let $A=P\,\mathrm{diag}(\lambda)P^T$ with $P$ orthogonal, and let $\alpha=\{i:\lambda_i>0\}$, $\beta=\{i:\lambda_i=0\}$, $\gamma=\{i:\lambda_i<0\}$. Let $U_{ij}=(\max\{\lambda_i,0\}+\max\{\lambda_j,0\})/(|\lambda_i|+|\lambda_j|)$ with $0/0:=1$. Then for any $V\in\partial_B\Pi_{\mathcal S^p_+}(A)$ there is $W\in\partial_B\Pi_{\mathcal S^{|\beta|}_+}(0)$ such that, for all $H\in\mathcal S^p$, with $\widetilde H:=P^THP$,
--
--   $$V(H)=P\begin{bmatrix}\widetilde H_{\alpha\alpha}&\widetilde H_{\alpha\beta}&U_{\alpha\gamma}\circ\widetilde H_{\alpha\gamma}\\ \widetilde H_{\alpha\beta}^T&W(\widetilde H_{\beta\beta})&0\\ \widetilde H_{\alpha\gamma}^T\circ U_{\alpha\gamma}^T&0&0\end{bmatrix}P^T \qquad(21)$$
--
--   ($\circ$ is the Hadamard product). Conversely, for any such $W$ there is such a $V$ satisfying (21). The same two statements hold with $\partial_B$ replaced by Clarke's generalized Jacobian $\partial$ on both sides.
--
--   **Formalization Note.** The block matrix is written entry by entry over the index sets $\alpha,\beta,\gamma$ (no ordering of eigenvalues is needed, cf. Remark 5); $\mathcal S^{|\beta|}$ is the symmetric matrices indexed by $\beta$.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 9, Proposition 4 (21)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem proposition_4 {n : Type} [Fintype n] [DecidableEq n]
    (A : SymMat n) (P : Matrix n n ℝ) (lam : n → ℝ)
    (hP : P ∈ Matrix.orthogonalGroup n ℝ)
    (hA : A.toMat = P * Matrix.diagonal lam * P.transpose) :
    (∀ V ∈ bJac (metricProj (psdCone n)) A,
      ∃ W ∈ bJac (metricProj (psdCone (betaIdx lam))) 0, Eq21 P lam V W) ∧
    (∀ W ∈ bJac (metricProj (psdCone (betaIdx lam))) 0,
      ∃ V ∈ bJac (metricProj (psdCone n)) A, Eq21 P lam V W) ∧
    (∀ V ∈ clarkeJac (metricProj (psdCone n)) A,
      ∃ W ∈ clarkeJac (metricProj (psdCone (betaIdx lam))) 0, Eq21 P lam V W) ∧
    (∀ W ∈ clarkeJac (metricProj (psdCone (betaIdx lam))) 0,
      ∃ V ∈ clarkeJac (metricProj (psdCone n)) A, Eq21 P lam V W) := by sorry
end SunNLSDP.Equiv
