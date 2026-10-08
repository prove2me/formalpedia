-- Prove2me | Theorems.Thm_RealTimeIter_Contract_mem_projTo_ball_of_dist
-- name    : RealTimeIter.Contract.mem_projTo_ball_of_dist
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:23.069861+00:00
-- url     : https://prove2.me/theorems/780061d2-6c7b-4bce-a272-c821a743f6ce
-- title:
--   §4, proof of Theorem 4.1 (Well definedness), p. 1722 — lifting: $\|z-\Pi^k\cdots\Pi^1y^0\|_k\le r\Rightarrow z\in\Pi^k\cdots\Pi^1\{\|y-y^0\|_0\le r\}$
-- statement:
--   Let $\|\cdot\|_k$ be compatible norms, $y^0\in\mathbb R^{n_0}$, $k\in\mathbb N$, $z\in\mathbb R^{n_k}$ and $r\in\mathbb R$. If $\|z-\Pi^k\cdots\Pi^1y^0\|_k\le r$, then
--   $$z\in\Pi^k\cdots\Pi^1\big\{y\in\mathbb R^{n_0}\ \big|\ \|y-y^0\|_0\le r\big\}.$$
--   The witness is $y':=y^0+(\Pi^k\cdots\Pi^1)^T(z-\Pi^k\cdots\Pi^1y^0)$, for which $\|y'-y^0\|_0=\|z-\Pi^k\cdots\Pi^1y^0\|_k$ by compatibility of the norms.
--
--   With $z=y^k$ and $r=\|\Delta y^0\|_0/(1-\delta_0)$ this places the real-time iterates in the projections of the ball $B_0$, which is (4.2).
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), p. 1722, §4, proof of Theorem 4.1 (Well definedness), the point y′ := y^0 + (Π^k⋯Π^1)^T(y^k − Π^k⋯Π^1 y^0)

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem
import Definitions.Def_RealTimeIter_Contract_Iteration

namespace RealTimeIter.Contract

theorem mem_projTo_ball_of_dist (P : OCP) (ν : CompatNorms P) (y0 : PD P 0) (k : ℕ)
    (z : PD P k) (r : ℝ) (hz : ν.nrm k (z - projTo P k y0) ≤ r) :
    z ∈ projTo P k '' {y | ν.nrm 0 (y - y0) ≤ r} := by sorry

end RealTimeIter.Contract
