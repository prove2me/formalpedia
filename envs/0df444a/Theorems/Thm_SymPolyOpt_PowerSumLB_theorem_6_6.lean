-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumLB_theorem_6_6
-- name    : SymPolyOpt.PowerSumLB.theorem_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:30.146978+00:00
-- url     : https://prove2.me/theorems/5ff49c12-9c1e-462d-9bbc-e426cc21fd58
-- title:
--   Theorem 6.6, p. 26 — min P_nmq ≥ L_nmq, and min P_nmq ≥ u_r(γ)ᵀ H_r(γ)⁻¹ u_r(γ) when q = m = 2r
-- statement:
--   Let $n, m, q \in \mathbb N$ with $m \le n+1$ and $m \le q \le 2n-2$, let $\gamma_1, \dots, \gamma_{m-1} \in \mathbb R$, and let $\mathrm P_{nmq}$ be the problem
--   $$\min \sum_{i=1}^n x_i^{\,q} \quad \text{s.t.} \quad \sum_{i=1}^n x_i^{\,j} = \gamma_j, \quad j = 1,\dots,m-1,$$
--   with optimal value $\min \mathrm P_{nmq}$ (an infimum, possibly $\pm\infty$). Then:
--
--   1. **(a)** $\min \mathrm P_{nmq} \ge \mathrm L_{nmq}$, where $\mathrm L_{nmq}$ is the value of the semidefinite program (6.5).
--   2. **(b)** If $q = m = 2r$, set $\gamma_0 = n$, let $H_r(\gamma) = (\gamma_{i+j-2})_{1\le i,j\le r}$ and $u_r(\gamma)^T = (\gamma_r, \dots, \gamma_{2r-1})$, so that $H_{r+1}(s) = \begin{pmatrix} H_r(\gamma) & u_r(\gamma) \\ u_r(\gamma)^T & s_{2r}\end{pmatrix}$. If $H_r(\gamma)$ is positive definite, then
--   $$\min \mathrm P_{nmq} \ge u_r(\gamma)^T H_r(\gamma)^{-1} u_r(\gamma).$$
--
--   Part (a) says that a single semidefinite constraint on an $n\times n$ Hankel matrix gives a lower bound on a symmetric polynomial optimization problem whose size does not grow with the degree; part (b) gives the bound in closed form in the even case.
--
--   **Formalization Note** The paper prints the bound of (b) as $u_r(\gamma)^T H_r(\gamma) u_r(\gamma)$, which is false: for $n = 2$, $m = q = 2$, $\gamma_1 = 1$ one has $\min \mathrm P = 1/2$ (at $x = (1/2,1/2)$) while $u^T H_1 u = n\gamma_1^2 = 2$. The paper's own proof (Schur complement on $H_{r+1}(s)$) gives the inverse, which is stated here. The hypothesis that $H_r(\gamma)$ is positive definite is added so that the inverse exists. All optimal values are infima in the extended reals. The bound $q \le 2n-2$ uses natural-number subtraction; for $n \le 1$ it forces $q = 0$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 26, Theorem 6.6

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting
open Matrix

namespace SymPolyOpt.PowerSumLB

/-- Theorem 6.6 (with (b) corrected to the inverse of H_r(γ)). -/
theorem theorem_6_6 (n m q : ℕ) (γ : ℕ → ℝ) (hm : m ≤ n + 1) (hmq : m ≤ q) (hq : q ≤ 2 * n - 2) :
    valL n m q γ ≤ minP n m q γ ∧
    ∀ r : ℕ, q = 2 * r → m = 2 * r → (hankel r (gammaExt n γ)).PosDef →
      (((fun i : Fin r => γ (r + i)) ⬝ᵥ
          ((hankel r (gammaExt n γ))⁻¹ *ᵥ fun i : Fin r => γ (r + i)) : ℝ) : EReal)
        ≤ minP n m q γ := by sorry

end SymPolyOpt.PowerSumLB
