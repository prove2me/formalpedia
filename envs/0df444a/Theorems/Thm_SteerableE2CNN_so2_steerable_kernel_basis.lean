-- Prove2me | Theorems.Thm_SteerableE2CNN_so2_steerable_kernel_basis
-- name    : SteerableE2CNN.so2_steerable_kernel_basis
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:41:08.760691+00:00
-- url     : https://prove2.me/theorems/30f37d0a-ac35-48e5-b068-0cc097195065
-- title:
--   Table 8: the basis of $\mathrm{SO}(2)$-steerable kernels
-- statement:
--   Let $m,n\in\mathbb{N}$ and let $\psi_m,\psi_n$ be the real irreps of $\mathrm{SO}(2)$ of frequencies $m$ and $n$: $\psi_0(r_\theta)=1$ and $\psi_k(r_\theta)=\psi(k\theta)$ for $k\ge1$. Let $\{b_\beta\}$ be the angular functions of Table 8, each of angular frequency $\mu_\beta$:
--
--   - $m=n=0$: $b(\phi)=[1]$, $\mu=0$;
--   - $m=0<n$: $b_\gamma(\phi)=[\cos(n\phi+\gamma),\ \sin(n\phi+\gamma)]$, $\gamma\in\{0,\pi/2\}$, $\mu=n$;
--   - $n=0<m$: $b_\gamma(\phi)=[\cos(m\phi+\gamma);\ \sin(m\phi+\gamma)]$, $\gamma\in\{0,\pi/2\}$, $\mu=m$;
--   - $m,n>0$: $b_{\gamma,s}(\phi)=\psi(\mu\phi+\gamma)\xi(s)$ with $\mu=m-sn$, $\gamma\in\{0,\pi/2\}$, $s\in\{\pm1\}$.
--
--   Then:
--
--   1. A kernel $\kappa:\mathbb{R}^2\to\mathbb{R}^{\dim\psi_m\times\dim\psi_n}$ satisfies
--
--   $$\kappa(r_\theta x)=\psi_m(r_\theta)\,\kappa(x)\,\psi_n(r_\theta)^{-1}\qquad\forall\theta\in\mathbb{R},\ x\in\mathbb{R}^2$$
--
--   if and only if there are radial functions $w_\beta:[0,\infty)\to\mathbb{R}$ such that $\kappa(x(r,\phi))=\sum_\beta w_\beta(r)\,b_\beta(\phi)$ for all $r\ge0$ and $\phi$, with $w_\beta(0)=0$ whenever $\mu_\beta\neq0$. At the origin only the frequency-$0$ elements survive (Appendix F.4.6).
--   2. The functions $b_\beta$ are linearly independent.
--
--   **Formalization Note** The paper works with square-integrable kernels and Fourier expansions. The Lean statement takes arbitrary functions and imposes the constraint at every point, as in eq. (2). The radial coefficients are then arbitrary functions. The Fourier coefficients $A_{\alpha\beta,\mu},B_{\alpha\beta,\mu}$ of eq. (5) do not appear.
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Section 2.5, eq. (5), p. 5; Appendix F.3, Table 8, p. 29; Appendix F.4.1, eqs. (24), (26), (28), (29), pp. 31-37; Appendix F.4.6, p. 48

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

open Matrix MeasureTheory

namespace SteerableE2CNN

theorem so2_steerable_kernel_basis (m n : ℕ)
    (κ : Plane → Matrix (Fin (so2Dim m)) (Fin (so2Dim n)) ℝ) :
    (KernelConstraint rotMat (so2Irrep m) (so2Irrep n) κ ↔
      ∃ w : Fin (so2BasisCard m n) → ℝ → ℝ,
        (∀ b, so2BasisFreq m n b ≠ 0 → w b 0 = 0) ∧
        ∀ r : ℝ, 0 ≤ r → ∀ φ : ℝ, κ (polar r φ) = ∑ b, w b r • so2Basis m n b φ) ∧
    LinearIndependent ℝ (so2Basis m n) := by sorry

end SteerableE2CNN
