-- Prove2me | Theorems.Thm_RobustLSAudit_Structured_residual_bound_iff_certificate
-- name    : RobustLSAudit.Structured.residual_bound_iff_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:01:43.866603+00:00
-- url     : https://prove2.me/theorems/dcc26522-6f4d-4176-b350-b4fbc7a8df41
-- title:
--   Eq. (29): exact residual certificate (corrected: τ ≥ 0 for p = 0)
-- statement:
--   Fix real matrices $A_0,\ldots,A_p\in\mathbb R^{n\times m}$, vectors $b_0,\ldots,b_p\in\mathbb R^n$, and a decision $x\in\mathbb R^m$. Let $r_S(x)=\max_{\|\delta\|_2\le1}\|A(\delta)x-b(\delta)\|_2$ for the affine families in Eq. (2). Set $a=A_0x-b_0$, $M=[A_1x-b_1\ \cdots\ A_px-b_p]$, $F=M^TM$, $g=M^Ta$, and $h=\|a\|_2^2$. For every real threshold $\lambda$,
--
--   $$
--   r_S(x)^2\le\lambda\iff\exists\tau\ge0:\quad \mathcal F(\lambda,\tau)=\begin{bmatrix}\lambda-\tau-h&-g^T\\-g&\tau I_p-F\end{bmatrix}\succeq0.
--   $$
--
--   This is the exact quadratic certificate used in the SDP reduction, retaining boundary semidefinite certificates. The uncertainty set is the entire continuous unit ball. No rank, consistency, or optimum-existence condition is assumed.
--
--   **Formalization Note** All data and the residual are the published source objects. The nonnegative multiplier is retained for the zero-dimensional uncertainty space. The source's initial sign assumption on $\lambda$ is redundant because both sides imply it.
--
--   Differences from the source:
--   - correction: Eq. (29) drops the explicit nonnegative multiplier → the certificate includes τ ≥ 0; reason: for p = 0, n = m = 1, A₀ = 0, b₀ = 2, λ = 0, τ = −4, the printed certificate is PSD although the squared residual is 4
--   - generalization: the preamble assumes λ ≥ 0 → λ is any real number; reason: both sides force λ ≥ 0, so negative thresholds make both sides false
--   - generalization: the usual positive-dimensional matrix presentation → all natural dimensions n, m, p, including zero, with the stated p = 0 repair; reason: every positive-dimensional instance is retained; n = 0 has zero residual, m = 0 has one decision, and p = 0 is ordinary least squares
--   - encoding: real finite-dimensional vectors and the Euclidean unit ball → Fin-indexed real vectors with the published explicit Euclidean norm and residual supremum; reason: zero-based indexing changes no data; the residual image of the continuous compact unit ball is nonempty, bounded, and attains its maximum
-- source:
--   El Ghaoui and Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), https://doi.org/10.1137/S0895479896298130, §4.1 Eq. (29) and its S-procedure preamble, printed pp. 1044–1045 / PDF pp. 10–11.

import Definitions.Def_RobustLS_Structured_Core
import Theorems.Thm_RobustLS_Structured_s_procedure_sufficient
import Theorems.Thm_RobustLS_Structured_s_procedure_lossless
import Theorems.Thm_RobustLS_Structured_worst_case_residual_sq_quadratic
import Theorems.Thm_RobustLS_Structured_s_procedure_step_eq29

namespace RobustLSAudit.Structured

/-- Eq. (29) and its S-procedure preamble, El Ghaoui--Lebret (1997), printed pp. 1044--1045 /
PDF pp. 10--11. Retain `τ ≥ 0` to cover `p = 0`, where the uncorrected matrix-only statement
is false (zero data, `λ = τ = -1`). The source's `λ ≥ 0` assumption is unnecessary:
both sides imply it. All finite dimensions, including zero, and all real thresholds are covered. -/
theorem residual_bound_iff_certificate {n m p : ℕ}
    (A0 : Matrix (Fin n) (Fin m) ℝ) (A : Fin p → Matrix (Fin n) (Fin m) ℝ)
    (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) (x : Fin m → ℝ) (lam : ℝ) :
    RobustLS.Structured.rS A0 A b0 b 1 x ^ 2 ≤ lam ↔
      ∃ τ : ℝ, 0 ≤ τ ∧ (RobustLS.Structured.calF A0 A b0 b x lam τ).PosSemidef := by sorry

end RobustLSAudit.Structured
