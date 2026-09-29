-- Prove2me | Theorems.Thm_RobustLS_Structured_worst_case_residual_sq_quadratic
-- name    : RobustLS.Structured.worst_case_residual_sq_quadratic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:35:01.044906+00:00
-- url     : https://prove2.me/theorems/410711e3-841a-4a69-aa21-d1a10a9c54bc
-- title:
--   §4.1, Eq. (28) — $r_S(\mathbf A,\mathbf b,x)^2$ is the maximum of a quadratic form over the unit ball
-- statement:
--   Fix the data $A_0,\dots,A_p$, $b_0,\dots,b_p$ and $x \in \mathbb{R}^m$, take $\rho = 1$, and let $F$, $g$, $h$ be as in (27): $F = M(x)^TM(x)$, $g = M(x)^T(A_0x - b_0)$, $h = \|A_0x - b_0\|^2$, where $M(x) = [A_1x - b_1\ \cdots\ A_px - b_p]$. Then
--
--   $$
--   r_S(\mathbf A,\mathbf b,x)^2 = \max_{\delta^T\delta \le 1} \begin{bmatrix} 1 \\ \delta \end{bmatrix}^T \begin{bmatrix} h & g^T \\ g & F \end{bmatrix} \begin{bmatrix} 1 \\ \delta \end{bmatrix},
--   $$
--
--   that is, the quadratic form on the right is at most $r_S(\mathbf A,\mathbf b,x)^2$ for every $\delta$ with $\delta^T\delta \le 1$, and equals it for some such $\delta$.
--
--   This rewrites the squared worst-case residual as the maximum of a convex quadratic function of $\delta$ over the Euclidean unit ball (a nonconvex maximization), the form to which the S-procedure applies.
--
--   **Formalization Note** The maximum is stated as "upper bound on the ball, attained on the ball". The vector $[1;\delta]$ and the block matrix are indexed by `Unit ⊕ Fin p`, the scalar first as printed. The statement holds for every $p \ge 0$.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1044, §4.1, Eq. (28)

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Eq. (28)** — El Ghaoui & Lebret (1997), §4.1, p. 1044 (PDF p. 10). With `ρ = 1` and
`F, g, h` as in (27),
`r_S(A, b, x)² = max_{δᵀδ ≤ 1} [1; δ]ᵀ [h gᵀ; g F] [1; δ]`.
The maximum is encoded as "an upper bound on the whole ball, attained at some `δ` of the ball". -/
theorem worst_case_residual_sq_quadratic {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) :
    (∀ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 →
        oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) ≤ rS A0 A b0 b 1 x ^ 2) ∧
      ∃ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 ∧
        oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) = rS A0 A b0 b 1 x ^ 2 := by sorry

end RobustLS.Structured
