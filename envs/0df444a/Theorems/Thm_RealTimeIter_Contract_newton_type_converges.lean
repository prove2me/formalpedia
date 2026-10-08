-- Prove2me | Theorems.Thm_RealTimeIter_Contract_newton_type_converges
-- name    : RealTimeIter.Contract.newton_type_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:27.735734+00:00
-- url     : https://prove2.me/theorems/ccf444f2-34f4-4c84-9fe0-5102a1bf7e88
-- title:
--   §4, proof of Theorem 4.1, p. 1723 — the Newton-type iterates from $y^k$ converge to $y^k_*\in B_k$ with $\nabla_y\mathcal L^k(y^k_*)=0$
-- statement:
--   Let $\|\cdot\|_k$ be compatible norms, $D_0\subset\mathbb R^{n_0}$ with $D_{k+1}=\Pi^{k+1}D_k$, $\kappa,\omega\in\mathbb R$ and $k\le N$. Assume, on $D_k$: $\mathcal L^k$ is twice continuously differentiable at every point, $J^k$ is continuous, $J^k(y)$ is invertible at every point, $\|J^k(y)^{-1}\|$ is bounded, and (4.1a), (4.1b) hold at level $k$. Let $x\in\mathbb R^{n_x}$ and $z\in D_k$, let $\Delta z$ be the Newton-type step of $P_k(x)$ at $z$, and put $\delta:=\kappa+\frac{\omega}{2}\|\Delta z\|_k$. If $\delta<1$ and the ball
--   $$B:=\Big\{y\in\mathbb R^{n_k}\ \Big|\ \|y-z\|_k\le\frac{\|\Delta z\|_k}{1-\delta}\Big\}$$
--   is contained in $D_k$, then the Newton-type iterates $y_0=z$, $y_{i+1}=y_i-J^k(y_i)^{-1}\nabla_y\mathcal L^k(y_i)$ converge to a point $y_*$ with
--   $$\|z-y_*\|_k\le\frac{\|\Delta z\|_k}{1-\delta}\qquad\text{and}\qquad\nabla_y\mathcal L^k(y_*)=0.$$
--
--   With $z=y^k$ this produces the exact stationary point $y^k_*$ of $P_k(x_k)$ and the first inequality of (4.4).
--
--   **Formalization Note.** The hypothesis $B\subseteq D_k$ is not stated in the paper; inside Theorem 4.1 it follows from (4.2) and the lifting step ($B_k\subseteq\Pi^k\cdots\Pi^1B_0\subseteq D_k$).
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), p. 1723, §4, proof of Theorem 4.1 (Distance to optimal solutions), the ball B_k and the limit y^k_*

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem
import Definitions.Def_RealTimeIter_Contract_Iteration

namespace RealTimeIter.Contract

theorem newton_type_converges (P : OCP) (ν : CompatNorms P) (D0 : Set (PD P 0)) (κ ω : ℝ)
    (k : ℕ) (hk : k ≤ P.N)
    (hc2 : ∀ y ∈ Dset P D0 k, ContDiffAt ℝ 2 (lagr P k 0) y)
    (hJc : ContinuousOn (J P k) (Dset P D0 k))
    (hinv : ∀ y ∈ Dset P D0 k, (J P k y).IsInvertible)
    (hbdd : ∃ β : ℝ, ∀ y ∈ Dset P D0 k, ‖(J P k y).inverse‖ ≤ β)
    (h41a : ∀ y' ∈ Dset P D0 k, ∀ y ∈ Dset P D0 k, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      y + t • (y' - y) ∈ Dset P D0 k →
      ν.nrm k ((J P k y').inverse
          ((J P k (y + t • (y' - y)) - hess P k (y + t • (y' - y))) (y' - y)))
        ≤ κ * ν.nrm k (y' - y))
    (h41b : ∀ y' ∈ Dset P D0 k, ∀ y ∈ Dset P D0 k, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      y + t • (y' - y) ∈ Dset P D0 k →
      ν.nrm k ((J P k y').inverse ((J P k (y + t • (y' - y)) - J P k y) (y' - y)))
        ≤ ω * t * ν.nrm k (y' - y) ^ 2)
    (x : Vec P.nx) (z : PD P k) (hz : z ∈ Dset P D0 k)
    (hδ : κ + ω / 2 * ν.nrm k (step P k x z) < 1)
    (hB : {y | ν.nrm k (y - z)
        ≤ ν.nrm k (step P k x z) / (1 - (κ + ω / 2 * ν.nrm k (step P k x z)))} ⊆ Dset P D0 k) :
    ∃ ystar : PD P k,
      Filter.Tendsto (newtonIter P k x z) Filter.atTop (nhds ystar) ∧
      ν.nrm k (z - ystar)
        ≤ ν.nrm k (step P k x z) / (1 - (κ + ω / 2 * ν.nrm k (step P k x z))) ∧
      grad P k x ystar = 0 := by sorry

end RealTimeIter.Contract
