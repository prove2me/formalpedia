-- Prove2me | Theorems.Thm_RealTimeIter_Contract_grad_transition
-- name    : RealTimeIter.Contract.grad_transition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:31.486523+00:00
-- url     : https://prove2.me/theorems/46229de1-731e-4342-8298-92a9f740b1e5
-- title:
--   §4, proof of Theorem 4.1, p. 1721 and footnote 2 — $\nabla_y\mathcal L^{k+1}(\Pi^{k+1}(y^k+\Delta y^k))=\Pi^{k+1}\nabla_y\mathcal L^k(y^k+\Delta y^k)$
-- statement:
--   Let $k\le N-1$, let $x\in\mathbb R^{n_x}$, and let $y,\Delta y\in\mathbb R^{n_k}$ satisfy the Newton-type equation $J^k(y)\Delta y=-\nabla_y\mathcal L^k(y)$ for problem $P_k(x)$. Assume $\mathcal L^k$ is twice continuously differentiable at $y$, $\mathcal L^k$ is differentiable at $y+\Delta y$, and $\mathcal L^{k+1}$ is differentiable at $\Pi^{k+1}(y+\Delta y)$. Write $u:=q_k+\Delta q_k$ for the control component of $y+\Delta y$ and $x_{k+1}:=f_k(x,u)$. Then
--
--   1. $s_k+\Delta s_k=x$ (footnote 2), and
--   2. $$\nabla_y\mathcal L^{k+1}\big(\Pi^{k+1}(y+\Delta y)\big)=\Pi^{k+1}\nabla_y\mathcal L^k(y+\Delta y),$$ where $\mathcal L^{k+1}$ is the Lagrangian of $P_{k+1}(x_{k+1})$.
--
--   This identity is how the shrinking horizon enters the contraction proof: after a real-time step, the gradient of the next problem at the shifted iterate is the projection of the current gradient at the updated iterate, provided the system moved undisturbed.
--
--   **Formalization Note.** The differentiability hypotheses are needed because Mathlib's gradient is $0$ at points of non-differentiability; in Theorem 4.1 they hold because the points lie in $D_k$, $D_{k+1}$.
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), p. 1721, §4, proof of Theorem 4.1 (Contraction property), display after (4.5), with footnote 2

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem
import Definitions.Def_RealTimeIter_Contract_Iteration

namespace RealTimeIter.Contract

theorem grad_transition (P : OCP) (k : ℕ) (hk : k < P.N) (x : Vec P.nx) (y Δ : PD P k)
    (hJ : J P k y Δ = -grad P k x y)
    (hc2 : ContDiffAt ℝ 2 (lagr P k 0) y)
    (hd : DifferentiableAt ℝ (lagr P k 0) (y + Δ))
    (hd' : DifferentiableAt ℝ (lagr P (k + 1) 0) (proj P k (y + Δ))) :
    sL P k k (y + Δ) = x ∧
      grad P (k + 1) (P.f k x (qL P k k (y + Δ))) (proj P k (y + Δ))
        = proj P k (grad P k x (y + Δ)) := by sorry

end RealTimeIter.Contract
