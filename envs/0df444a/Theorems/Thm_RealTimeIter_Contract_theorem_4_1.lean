-- Prove2me | Theorems.Thm_RealTimeIter_Contract_theorem_4_1
-- name    : RealTimeIter.Contract.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:37.595994+00:00
-- url     : https://prove2.me/theorems/0f782377-97e0-4562-b65c-20db0b022019
-- title:
--   Theorem 4.1, pp. 1720–1721 — local contractivity of the real-time iterations: (4.2), (4.3), (4.4)
-- statement:
--   Consider the shrinking-horizon problems $P_k(x_k)$, their Lagrangians $\mathcal L^k$ and Newton-type matrices $J^k$, a family of compatible norms $\|\cdot\|_k$, a neighbourhood $D_0\subset\mathbb R^{n_0}$ with projections $D_{k+1}:=\Pi^{k+1}D_k$, an initial state $x_0$ and an initial guess $y^0\in D_0$. Assume, for $k=0,\dots,N$: $\mathcal L^k$ is twice continuously differentiable on $D_k$; $J^k$ is continuous on $D_k$ and has a bounded inverse there; and there are $\kappa<1$ and $\omega\in\mathbb R$ such that (4.1a), (4.1b) hold for all $y',y\in D_k$, $\Delta y=y'-y$, $t\in[0,1]$, and (4.1c) holds for $k\le N-1$:
--   $$\big\|J^k(y')^{-1}\big(J^k(y+t\Delta y)-\nabla^2_y\mathcal L^k(y+t\Delta y)\big)\Delta y\big\|_k\le\kappa\|\Delta y\|_k,$$
--   $$\big\|J^k(y')^{-1}\big(J^k(y+t\Delta y)-J^k(y)\big)\Delta y\big\|_k\le\omega t\|\Delta y\|_k^2,$$
--   $$\big\|J^{k+1}(\Pi^{k+1}y')^{-1}\Pi^{k+1}\big(J^k(y+t\Delta y)-J^k(y)\big)\Delta y\big\|_{k+1}\le\omega t\|\Delta y\|_k^2.$$
--   Suppose the first step is small, $\delta_0:=\kappa+\frac{\omega}{2}\|\Delta y^0\|_0<1$, and $B_0=\{y:\|y-y^0\|_0\le\|\Delta y^0\|_0/(1-\delta_0)\}\subseteq D_0$. Let $y^0,\dots,y^N$ be the real-time iterates, $\Delta y^k:=-J^k(y^k)^{-1}\nabla_y\mathcal L^k(y^k)$, $y^{k+1}:=\Pi^{k+1}(y^k+\Delta y^k)$, where $\mathcal L^k$ belongs to $P_k(x_k)$ and $x_{k+1}=f_k(x_k,u_k)$, $u_k:=q^k_k+\Delta q^k_k$, and let $\delta_k:=\kappa+\frac{\omega}{2}\|\Delta y^k\|_k$. Then:
--
--   1. **(4.2)** for $k=0,\dots,N$: $y^k\in\Pi^k\cdots\Pi^1B_0\subseteq D_k$;
--   2. **(4.3)** for $k=0,\dots,N-1$: $$\|\Delta y^{k+1}\|_{k+1}\le\Big(\kappa+\frac{\omega}{2}\|\Delta y^k\|_k\Big)\|\Delta y^k\|_k=\delta_k\|\Delta y^k\|_k\le\delta_0\|\Delta y^k\|_k,$$ and $\delta_k\le\delta_0$;
--   3. **(4.4)** for $k=0,\dots,N$: the Newton-type iterates (2.4) of $P_k(x_k)$ started at $y^k$ converge to a stationary point $y^k_*$ ($\nabla_y\mathcal L^k(y^k_*)=0$), and $$\|y^k-y^k_*\|_k\le\frac{\|\Delta y^k\|_k}{1-\delta_k}\le\frac{(\delta_0)^k\|\Delta y^0\|_0}{1-\delta_0}.$$
--
--   The real-time iteration performs a single Newton-type step per problem and then moves to the next, shorter problem. The theorem shows that, after one initial disturbance, its iterates contract like a Newton-type method and approach the exact stationary points of the problems they track, at a geometric rate.
--
--   **Formalization Note.** The hypotheses are bundled in `Thm41Hyp` (see the definitions file): differentiability, continuity and invertibility are required at the points of $D_k$, not globally; (4.1a)–(4.1c) are required for those $t$ with $y+t\Delta y\in D_k$, since the paper's $J^k,\mathcal L^k$ live on $D_k$ (which need not be convex). $y^k_*$ is identified as the limit of the Newton-type scheme (2.4) from $y^k$, as in the paper's proof (p. 1723), so it cannot be chosen after the fact. Since $x_k$ enters $\mathcal L^k$ linearly, its Hessian and $J^k$ do not depend on $x_k$ (Remark 1).
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), pp. 1720–1721, Theorem 4.1, (4.1a)–(4.4)

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem
import Definitions.Def_RealTimeIter_Contract_Iteration

namespace RealTimeIter.Contract

theorem theorem_4_1 (P : OCP) (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0)
    (D0 : Set (PD P 0)) (κ ω : ℝ) (h : Thm41Hyp P ν x0 y0 D0 κ ω) :
    -- (4.2)
    (∀ k ≤ P.N, (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω ∧
        projTo P k '' ball0 P ν x0 y0 κ ω ⊆ Dset P D0 k) ∧
    -- (4.3)
    (∀ k < P.N,
        ν.nrm (k + 1) (rtiStep P x0 y0 (k + 1))
          ≤ (κ + ω / 2 * ν.nrm k (rtiStep P x0 y0 k)) * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k * ν.nrm k (rtiStep P x0 y0 k)
          ≤ delta P ν x0 y0 κ ω 0 * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k ≤ delta P ν x0 y0 κ ω 0) ∧
    -- (4.4)
    (∀ k ≤ P.N, ∃ ystar : PD P k,
        Filter.Tendsto (newtonIter P k (rti P x0 y0 k).1 (rti P x0 y0 k).2) Filter.atTop
          (nhds ystar) ∧
        grad P k (rti P x0 y0 k).1 ystar = 0 ∧
        ν.nrm k ((rti P x0 y0 k).2 - ystar)
          ≤ ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k) ∧
        ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k)
          ≤ delta P ν x0 y0 κ ω 0 ^ k * ν.nrm 0 (rtiStep P x0 y0 0)
              / (1 - delta P ν x0 y0 κ ω 0)) := by sorry

end RealTimeIter.Contract
