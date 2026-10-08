-- Prove2me | Theorems.Thm_RealTimeIter_Contract_one_step_contraction
-- name    : RealTimeIter.Contract.one_step_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:31.135657+00:00
-- url     : https://prove2.me/theorems/ec6f9852-bd61-477c-888a-f940f4123c7c
-- title:
--   §4, proof of Theorem 4.1, p. 1722 — the left inequality of (4.3): $\|\Delta y^{k+1}\|_{k+1}\le\kappa\|\Delta y^k\|_k+\frac12\omega\|\Delta y^k\|_k^2$
-- statement:
--   Let $\|\cdot\|_k$ be compatible norms, $D_0\subset\mathbb R^{n_0}$ with $D_{k+1}=\Pi^{k+1}D_k$, $\kappa,\omega\in\mathbb R$ and $k\le N-1$. Assume:
--
--   1. $\mathcal L^k$ is twice continuously differentiable at every point of $D_k$, and $\mathcal L^{k+1}$ at every point of $D_{k+1}$;
--   2. $J^k(y)$ is invertible for every $y\in D_k$;
--   3. (4.1a) holds at levels $k$ and $k+1$, and (4.1c) holds at level $k$ (for $t\in[0,1]$ with $y+t\Delta y$ in the domain).
--
--   Let $x\in\mathbb R^{n_x}$, $y\in D_k$, let $\Delta y:=-J^k(y)^{-1}\nabla_y\mathcal L^k(y)$ be the step of $P_k(x)$, and assume the segment $[y,y+\Delta y]$ lies in $D_k$. Let $x_{k+1}:=f_k(x,q_k+\Delta q_k)$ and let $\Delta y^{+}$ be the step of $P_{k+1}(x_{k+1})$ at $\Pi^{k+1}(y+\Delta y)$. Then
--   $$\|\Delta y^{+}\|_{k+1}\le\Big(\kappa+\frac{\omega}{2}\|\Delta y\|_k\Big)\|\Delta y\|_k.$$
--
--   This is the one-step contraction of the real-time iteration, the left inequality of (4.3).
--
--   **Formalization Note.** The segment hypothesis is not in the paper; inside Theorem 4.1 it holds because the segment lies in $\Pi^k\cdots\Pi^1B_0\subseteq D_k$. It replaces the convexity the paper uses implicitly. (4.1a) at level $k$ is a hypothesis of Theorem 4.1; it is included here so that no sign assumption on $\kappa$ is needed.
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), p. 1722, §4, proof of Theorem 4.1 (Contraction property), left inequality of (4.3), from (4.6), (4.1a), (4.1c)

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem
import Definitions.Def_RealTimeIter_Contract_Iteration

namespace RealTimeIter.Contract

theorem one_step_contraction (P : OCP) (ν : CompatNorms P) (D0 : Set (PD P 0)) (κ ω : ℝ)
    (k : ℕ) (hk : k < P.N)
    (hc2 : ∀ y ∈ Dset P D0 k, ContDiffAt ℝ 2 (lagr P k 0) y)
    (hc2' : ∀ y ∈ Dset P D0 (k + 1), ContDiffAt ℝ 2 (lagr P (k + 1) 0) y)
    (hinv : ∀ y ∈ Dset P D0 k, (J P k y).IsInvertible)
    (h41a : ∀ y' ∈ Dset P D0 k, ∀ y ∈ Dset P D0 k, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      y + t • (y' - y) ∈ Dset P D0 k →
      ν.nrm k ((J P k y').inverse
          ((J P k (y + t • (y' - y)) - hess P k (y + t • (y' - y))) (y' - y)))
        ≤ κ * ν.nrm k (y' - y))
    (h41a' : ∀ y' ∈ Dset P D0 (k + 1), ∀ y ∈ Dset P D0 (k + 1), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      y + t • (y' - y) ∈ Dset P D0 (k + 1) →
      ν.nrm (k + 1) ((J P (k + 1) y').inverse
          ((J P (k + 1) (y + t • (y' - y)) - hess P (k + 1) (y + t • (y' - y))) (y' - y)))
        ≤ κ * ν.nrm (k + 1) (y' - y))
    (h41c : ∀ y' ∈ Dset P D0 k, ∀ y ∈ Dset P D0 k, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      y + t • (y' - y) ∈ Dset P D0 k →
      ν.nrm (k + 1) ((J P (k + 1) (proj P k y')).inverse
          (proj P k ((J P k (y + t • (y' - y)) - J P k y) (y' - y))))
        ≤ ω * t * ν.nrm k (y' - y) ^ 2)
    (x : Vec P.nx) (y : PD P k) (hy : y ∈ Dset P D0 k)
    (hseg : segment ℝ y (y + step P k x y) ⊆ Dset P D0 k) :
    ν.nrm (k + 1) (step P (k + 1) (P.f k x (qL P k k (y + step P k x y)))
        (proj P k (y + step P k x y)))
      ≤ (κ + ω / 2 * ν.nrm k (step P k x y)) * ν.nrm k (step P k x y) := by sorry

end RealTimeIter.Contract
