-- Prove2me | Theorems.Thm_RobustLS_Structured_srls_sdp_exact
-- name    : RobustLS.Structured.srls_sdp_exact
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:37:07.255011+00:00
-- url     : https://prove2.me/theorems/c2f2d4ef-adb5-451c-a678-a550d2b74351
-- title:
--   Theorem 4.2 — structured robust least squares is solved exactly by the SDP (32)
-- statement:
--   Let $A_0,\dots,A_p \in \mathbb{R}^{n\times m}$, $b_0,\dots,b_p \in \mathbb{R}^n$ with $p \ge 1$, take $\rho = 1$, and let $M(x) = [A_1x - b_1\ \cdots\ A_px - b_p]$. Consider the semidefinite program in $(\lambda,\tau,x)$
--
--   $$
--   \text{minimize } \lambda \quad\text{subject to}\quad \begin{bmatrix} \lambda - \tau & 0 & (A_0x - b_0)^T \\ 0 & \tau I & M(x)^T \\ A_0x - b_0 & M(x) & I \end{bmatrix} \succeq 0. \tag{32}
--   $$
--
--   Then:
--
--   1. for every $x \in \mathbb{R}^m$ and $\lambda \in \mathbb{R}$, some $\tau$ makes $(\lambda,\tau,x)$ feasible for (32) if and only if $r_S(\mathbf A,\mathbf b,x)^2 \le \lambda$;
--   2. $(\lambda,\tau,x)$ is an optimal solution of (32) if and only if $x$ is an SRLS solution (it minimizes $r_S(\mathbf A,\mathbf b,\cdot)$ over $\mathbb{R}^m$), $\lambda = r_S(\mathbf A,\mathbf b,x)^2$, and $(\lambda,\tau,x)$ is feasible for (32).
--
--   This makes precise the paper's statement that "the Euclidean-norm SRLS can be solved by computing an optimal solution $(\lambda,\tau,x)$ of the SDP (32)": the $x$-component of any optimal solution is an SRLS solution and the optimal value is the squared optimal worst-case residual, and conversely. A min–max problem over an ellipsoidal family of affinely perturbed systems thus reduces to one convex semidefinite program, solvable in polynomial time.
--
--   **Formalization Note** $\lambda$ in (32) is the *squared* residual. Optimality means feasibility plus $\lambda \le \lambda'$ for every feasible $(\lambda',\tau',x')$. The paper does not state $p \ge 1$, but needs it: for $p = 0$ the $\tau I$ block is empty, $\tau$ is unconstrained and every $\lambda$ is feasible, so (32) has no optimal solution. The existence of an optimal solution is not asserted (the paper does not assert it).
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1045, §4.2, Theorem 4.2, Eq. (32)

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Theorem 4.2** — El Ghaoui & Lebret (1997), §4.2, p. 1045 (PDF p. 11). When `ρ = 1`, the
Euclidean-norm SRLS can be solved by computing an optimal solution `(λ, τ, x)` of the SDP (32)
"minimize `λ` subject to `[λ − τ, 0, (A₀x − b₀)ᵀ; 0, τI, M(x)ᵀ; A₀x − b₀, M(x), I] ⪰ 0`".
Made precise as:
(a) for every `x` and `λ`, some `τ` makes `(λ, τ, x)` feasible for (32) iff `r_S(A, b, x)² ≤ λ`;
(b) `(λ, τ, x)` is an optimal solution of (32) iff `x` is an SRLS solution (minimizes
`r_S(A, b, ·)` over `ℝ^m`), `λ = r_S(A, b, x)²` and `(λ, τ, x)` is feasible for (32).
The hypothesis `1 ≤ p` is not written in the paper but is needed: for `p = 0` the `τI` block is
empty and every `λ` is feasible for (32) (take `τ` very negative). -/
theorem srls_sdp_exact {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) :
    (∀ (x : Fin m → ℝ) (lam : ℝ),
        (∃ τ : ℝ, SDP32Feasible A0 A b0 b lam τ x) ↔ rS A0 A b0 b 1 x ^ 2 ≤ lam) ∧
      ∀ (lam τ : ℝ) (x : Fin m → ℝ),
        SDP32Optimal A0 A b0 b lam τ x ↔
          IsSRLSSolution A0 A b0 b 1 x ∧ lam = rS A0 A b0 b 1 x ^ 2 ∧
            SDP32Feasible A0 A b0 b lam τ x := by sorry

end RobustLS.Structured
