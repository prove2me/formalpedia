-- Prove2me | Theorems.Thm_RobustLS_Structured_worst_case_residual_sdp
-- name    : RobustLS.Structured.worst_case_residual_sdp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:36:04.943987+00:00
-- url     : https://prove2.me/theorems/b4608c09-844d-4ba9-9d51-e8a38e2643ab
-- title:
--   Theorem 4.1 (first assertion) — $r_S(\mathbf A,\mathbf b,x)^2$ is the value of the SDP minimize $\lambda$ subject to (29)
-- statement:
--   Fix the data and $x \in \mathbb{R}^m$, take $\rho = 1$, let $F$, $g$, $h$ be as in (27), and assume $p \ge 1$. Then the squared worst-case residual is the optimal value of the semidefinite program in the two scalar variables $(\lambda,\tau)$
--
--   $$
--   \text{minimize } \lambda \quad \text{subject to} \quad \mathcal F(\lambda,\tau) = \begin{bmatrix} \lambda - \tau - h & -g^T \\ -g & \tau I - F \end{bmatrix} \succeq 0,
--   $$
--
--   and the minimum is attained: every feasible $(\lambda,\tau)$ has $\lambda \ge r_S(\mathbf A,\mathbf b,x)^2$, and $\lambda = r_S(\mathbf A,\mathbf b,x)^2$ is feasible for some $\tau$.
--
--   The worst-case residual, a maximum of a nonconcave function over a ball, is thereby computed exactly by a convex problem of fixed small size.
--
--   **Formalization Note** Only the first assertion of Theorem 4.1 is formalized; the one-dimensional reformulation (30)–(31) and the description of the worst-case perturbation are not (they rely on the notion "$(F,g)$-controllable", which the paper does not define). The hypothesis $p \ge 1$ is not written in the paper but is needed: for $p = 0$ every $\lambda$ is feasible and the minimum does not exist.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1045, §4.1, Theorem 4.1 (first assertion)

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Theorem 4.1, first assertion (the two-variable SDP)** — El Ghaoui & Lebret (1997), §4.1,
p. 1045 (PDF p. 11). For every fixed `x`, the squared worst-case residual (for `ρ = 1`)
`r_S(A, b, x)²` is the optimal value of the SDP in two variables "minimize `λ` subject to (29)":
every `λ` for which some `τ` makes `𝓕(λ, τ) ⪰ 0` satisfies `λ ≥ r_S(A, b, x)²`, and
`λ = r_S(A, b, x)²` is feasible (the minimum is attained).
The paper's second and third assertions ((30)–(31) and the worst-case `δ`) are not formalized.
The hypothesis `1 ≤ p` is not written in the paper but is needed: for `p = 0` every `λ` is
feasible for (29). -/
theorem worst_case_residual_sdp {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) :
    (∀ lam τ : ℝ, (calF A0 A b0 b x lam τ).PosSemidef → rS A0 A b0 b 1 x ^ 2 ≤ lam) ∧
      ∃ τ : ℝ, (calF A0 A b0 b x (rS A0 A b0 b 1 x ^ 2) τ).PosSemidef := by sorry

end RobustLS.Structured
