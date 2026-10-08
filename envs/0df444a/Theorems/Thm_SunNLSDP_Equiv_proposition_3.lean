-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_proposition_3
-- name    : SunNLSDP.Equiv.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:39:20.756851+00:00
-- url     : https://prove2.me/theorems/88e69660-87bf-46ac-993a-60fa137a760f
-- title:
--   Proposition 3, p. 8 — differentiability of Π_{S^p_+} and of Π′_{S^p_+}(A;·), and ∂_BΠ_{S^p_+}(A) = ∂_BΠ′_{S^p_+}(A;·)(0)
-- statement:
--   Let $\Pi=\Pi_{\mathcal S^p_+}$ be the metric projector onto the positive semidefinite cone. Then:
--
--   1. $\Pi$ is Fréchet differentiable at $A\in\mathcal S^p$ if and only if $A$ is nonsingular.
--   2. Let $A\in\mathcal S^p$ have the spectral decomposition $A=P\Lambda P^T$ with $P$ orthogonal, $\Lambda=\mathrm{diag}(\lambda)$, and $\beta=\{i:\lambda_i=0\}$. The directional derivative $\Pi'(A;\cdot)$ is Fréchet differentiable at $H\in\mathcal S^p$ if and only if $\widetilde H_{\beta\beta}$ is nonsingular, where $\widetilde H:=P^THP$.
--   3. For every $A\in\mathcal S^p$, with $\Phi(\cdot):=\Pi'(A;\cdot)$,
--   $$\partial_B\Pi(A)=\partial_B\Phi(0).$$
--
--   **Formalization Note.** When $\beta=\emptyset$ the matrix $\widetilde H_{\beta\beta}$ is empty and counts as nonsingular. $\Pi'(A;H)$ is the one-sided directional derivative.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 8, Proposition 3 (citing Pang, Sun and Sun [24, Corollary 10 & Lemma 11])

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem proposition_3 {n : Type} [Fintype n] [DecidableEq n] :
    (∀ A : SymMat n, DifferentiableAt ℝ (metricProj (psdCone n)) A ↔ A.toMat.det ≠ 0) ∧
    (∀ (A : SymMat n) (P : Matrix n n ℝ) (lam : n → ℝ), P ∈ Matrix.orthogonalGroup n ℝ →
      A.toMat = P * Matrix.diagonal lam * P.transpose →
      ∀ H : SymMat n,
        (DifferentiableAt ℝ (NonsmoothNewton.Local.dirDeriv (metricProj (psdCone n)) A) H ↔
          ((P.transpose * H.toMat * P).submatrix (fun i : betaIdx lam => (i : n))
            (fun i : betaIdx lam => (i : n))).det ≠ 0)) ∧
    (∀ A : SymMat n, bJac (metricProj (psdCone n)) A =
      bJac (NonsmoothNewton.Local.dirDeriv (metricProj (psdCone n)) A) 0) := by sorry
end SunNLSDP.Equiv
