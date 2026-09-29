-- Prove2me | Theorems.Thm_RobustLS_Structured_sdp32_iff_calF
-- name    : RobustLS.Structured.sdp32_iff_calF
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:36:36.872309+00:00
-- url     : https://prove2.me/theorems/c5981b41-f4ca-4990-bad6-95e7ee121c53
-- title:
--   §4.2, Schur-complement step — the LMI of (32) is equivalent to (29)
-- statement:
--   Fix the data, $x \in \mathbb{R}^m$, and scalars $\lambda$, $\tau$; let $M(x)$ be as in (26) and $F$, $g$, $h$ as in (27). Then
--
--   $$
--   \begin{bmatrix} \lambda - \tau & 0 & (A_0x - b_0)^T \\ 0 & \tau I & M(x)^T \\ A_0x - b_0 & M(x) & I \end{bmatrix} \succeq 0
--   \quad\Longleftrightarrow\quad
--   \mathcal F(\lambda,\tau) = \begin{bmatrix} \lambda - \tau - h & -g^T \\ -g & \tau I - F \end{bmatrix} \succeq 0 .
--   $$
--
--   The right-hand side is the Schur complement of the identity block in the left-hand side. Unlike (29), the left-hand matrix is affine in $x$ as well as in $(\lambda,\tau)$, which is what allows the minimization over $x$ to be folded into a single SDP.
--
--   **Formalization Note** The $(1+p+n)$-square matrix is indexed by `(Unit ⊕ Fin p) ⊕ Fin n`, blocks in the printed order. The statement holds for every $p \ge 0$.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1045, §4.2 (sentence introducing Theorem 4.2) and Eq. (32)

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **§4.2, the Schur-complement step** — El Ghaoui & Lebret (1997), §4.2, p. 1045 (PDF p. 11):
"Using Theorem 4.1, the expression of F, g, h given in (27), and Schur complements, we obtain the
following result." For all `λ, τ, x`, the matrix of the SDP (32),
`[λ − τ, 0, (A₀x − b₀)ᵀ; 0, τI, M(x)ᵀ; A₀x − b₀, M(x), I]`, is positive semidefinite if and only if
`𝓕(λ, τ) = [λ − τ − h, −gᵀ; −g, τI − F]` of (29), built from `x` via (27), is. -/
theorem sdp32_iff_calF {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (lam τ : ℝ) (x : Fin m → ℝ) :
    SDP32Feasible A0 A b0 b lam τ x ↔ (calF A0 A b0 b x lam τ).PosSemidef := by sorry

end RobustLS.Structured
