-- Prove2me | Theorems.Thm_RealTimeIter_Contract_block_identity
-- name    : RealTimeIter.Contract.block_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:10.854971+00:00
-- url     : https://prove2.me/theorems/7b0161dc-49a2-4f12-9fbe-24ff966b19c0
-- title:
--   §4, proof of Theorem 4.1, p. 1722 — $\Pi^{k+1}(\nabla^2_y\mathcal L^k(y)-J^k(y))=(\nabla^2_{\tilde y}\mathcal L^{k+1}(\tilde y)-J^{k+1}(\tilde y))\Pi^{k+1}$
-- statement:
--   Let $k\le N-1$ and $y\in\mathbb R^{n_k}$, and write $\tilde y:=\Pi^{k+1}y$. Assume $\mathcal L^k$ is twice continuously differentiable at $y$ and $\mathcal L^{k+1}$ is twice continuously differentiable at $\tilde y$. Then
--   $$\Pi^{k+1}\big(\nabla^2_y\mathcal L^k(y)-J^k(y)\big)=\big(\nabla^2_{\tilde y}\mathcal L^{k+1}(\tilde y)-J^{k+1}(\tilde y)\big)\,\Pi^{k+1}.$$
--   In block form: the first three block columns $(\lambda_k,s_k,q_k)$ of the left-hand side vanish, and the remaining block is $\nabla^2_{\tilde y}\mathcal L^{k+1}(\tilde y)-J^{k+1}(\tilde y)$.
--
--   The Hessian error of the current problem, seen from the next problem, is exactly the Hessian error of the next problem; this lets assumption (4.1a) at level $k+1$ control the error term of the real-time step at level $k$.
--
--   **Formalization Note.** The same stage approximations $Q^H_i, M^H_i, R^H_i$ enter $J^k$ and $J^{k+1}$, as in §2.1. The equality is between linear maps $\mathbb R^{n_k}\to\mathbb R^{n_{k+1}}$.
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), p. 1722, §4, proof of Theorem 4.1 (Contraction property), first display

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem
import Definitions.Def_RealTimeIter_Contract_Iteration

namespace RealTimeIter.Contract

theorem block_identity (P : OCP) (k : ℕ) (hk : k < P.N) (y : PD P k)
    (hc2 : ContDiffAt ℝ 2 (lagr P k 0) y)
    (hc2' : ContDiffAt ℝ 2 (lagr P (k + 1) 0) (proj P k y)) :
    (proj P k).comp (hess P k y - J P k y)
      = (hess P (k + 1) (proj P k y) - J P (k + 1) (proj P k y)).comp (proj P k) := by sorry

end RealTimeIter.Contract
