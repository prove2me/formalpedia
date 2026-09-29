-- Prove2me | Theorems.Thm_RobustLS_Structured_s_procedure_step_eq29
-- name    : RobustLS.Structured.s_procedure_step_eq29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:35:32.14174+00:00
-- url     : https://prove2.me/theorems/1ca20ce2-6207-4fef-a52c-a28c95ebecba
-- title:
--   §4.1, Eq. (29) — the worst-case bound $\le\lambda$ holds iff $\mathcal F(\lambda,\tau)\succeq 0$ for some $\tau$
-- statement:
--   Fix the data and $x$, let $F$, $g$, $h$ be as in (27), assume $p \ge 1$, and let $\lambda \ge 0$. Then
--
--   $$
--   \begin{bmatrix} 1 \\ \delta \end{bmatrix}^T \begin{bmatrix} h & g^T \\ g & F \end{bmatrix} \begin{bmatrix} 1 \\ \delta \end{bmatrix} \le \lambda \quad \text{for every } \delta \text{ with } \delta^T\delta \le 1
--   $$
--
--   if and only if there exists a scalar $\tau$ such that
--
--   $$
--   \mathcal F(\lambda,\tau) = \begin{bmatrix} \lambda - \tau - h & -g^T \\ -g & \tau I - F \end{bmatrix} \succeq 0 .
--   $$
--
--   This is the step at which the S-procedure (Lemma 2.1 with one constraint $1 - \delta^T\delta \ge 0$) converts a condition quantified over the unit ball into a linear matrix inequality in two scalar variables.
--
--   **Formalization Note** The paper does not state $p \ge 1$, but needs it: for $p = 0$ the block $\tau I - F$ is empty, $\tau$ is unconstrained and $\mathcal F(\lambda,\tau) \succeq 0$ for every $\lambda$ once $\tau$ is small enough, so the right-hand side would hold for every $\lambda$. The paper's "$\tau \ge 0$" is not a separate constraint because, for $p \ge 1$, $\tau I \succeq F \succeq 0$ implies it. The hypothesis $\lambda \ge 0$ is kept as printed ("Now let $\lambda \ge 0$").
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), pp. 1044–1045, §4.1, Eq. (29)

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **The S-procedure step, Eq. (29)** — El Ghaoui & Lebret (1997), §4.1, pp. 1044–1045
(PDF pp. 10–11). Let `λ ≥ 0` and `F, g, h` as in (27). Then
`[1; δ]ᵀ [h gᵀ; g F] [1; δ] ≤ λ` for every `δ` with `δᵀδ ≤ 1` if and only if there is a scalar
`τ` with `𝓕(λ, τ) = [λ − τ − h, −gᵀ; −g, τI − F] ⪰ 0`.
The hypothesis `1 ≤ p` is not written in the paper but is needed: for `p = 0` the block `τI − F`
is empty, `τ` is unconstrained and (29) holds for every `λ` (take `τ` very negative). -/
theorem s_procedure_step_eq29 {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∀ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 → oneStack δ ⬝ᵥ (hgFBlock A0 A b0 b x *ᵥ oneStack δ) ≤ lam) ↔
      ∃ τ : ℝ, (calF A0 A b0 b x lam τ).PosSemidef := by sorry

end RobustLS.Structured
