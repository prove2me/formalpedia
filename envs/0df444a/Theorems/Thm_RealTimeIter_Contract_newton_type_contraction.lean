-- Prove2me | Theorems.Thm_RealTimeIter_Contract_newton_type_contraction
-- name    : RealTimeIter.Contract.newton_type_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:34.734195+00:00
-- url     : https://prove2.me/theorems/013e850b-30ed-499e-8afe-407e72f1077e
-- title:
--   (4.7), proof of Theorem 4.1, p. 1723 — $\|\Delta y^k_{i+1}\|_k\le(\kappa+\frac{\omega}{2}\|\Delta y^k_i\|_k)\|\Delta y^k_i\|_k$
-- statement:
--   Let $\|\cdot\|_k$ be compatible norms, $D_0\subset\mathbb R^{n_0}$ with $D_{k+1}=\Pi^{k+1}D_k$, $\kappa,\omega\in\mathbb R$ and $k\le N$. Assume $\mathcal L^k$ is twice continuously differentiable at every point of $D_k$, $J^k(y)$ is invertible for $y\in D_k$, and (4.1a), (4.1b) hold at level $k$. Let $x\in\mathbb R^{n_x}$ and $z\in D_k$, let $\Delta z:=-J^k(z)^{-1}\nabla_y\mathcal L^k(z)$ be the Newton-type step of $P_k(x)$ at $z$, and assume the segment $[z,z+\Delta z]$ lies in $D_k$. Then the next step $\Delta z^{+}:=-J^k(z+\Delta z)^{-1}\nabla_y\mathcal L^k(z+\Delta z)$ satisfies
--   $$\|\Delta z^{+}\|_k\le\Big(\kappa+\frac{\omega}{2}\|\Delta z\|_k\Big)\|\Delta z\|_k.$$
--
--   This is the contraction of the full Newton-type method (2.4) on a fixed problem, the step that lets the proof construct the exact stationary point $y^k_*$.
--
--   **Formalization Note.** The segment hypothesis replaces the paper's implicit convexity; in the proof of Theorem 4.1 the iterates stay in the convex ball $B_k\subseteq D_k$.
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), p. 1723, §4, proof of Theorem 4.1 (Distance to optimal solutions), (4.7)

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem
import Definitions.Def_RealTimeIter_Contract_Iteration

namespace RealTimeIter.Contract

theorem newton_type_contraction (P : OCP) (ν : CompatNorms P) (D0 : Set (PD P 0)) (κ ω : ℝ)
    (k : ℕ) (hk : k ≤ P.N)
    (hc2 : ∀ y ∈ Dset P D0 k, ContDiffAt ℝ 2 (lagr P k 0) y)
    (hinv : ∀ y ∈ Dset P D0 k, (J P k y).IsInvertible)
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
    (hseg : segment ℝ z (z + step P k x z) ⊆ Dset P D0 k) :
    ν.nrm k (step P k x (z + step P k x z))
      ≤ (κ + ω / 2 * ν.nrm k (step P k x z)) * ν.nrm k (step P k x z) := by sorry

end RealTimeIter.Contract
