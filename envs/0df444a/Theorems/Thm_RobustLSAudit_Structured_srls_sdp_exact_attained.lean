-- Prove2me | Theorems.Thm_RobustLSAudit_Structured_srls_sdp_exact_attained
-- name    : RobustLSAudit.Structured.srls_sdp_exact_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:08:28.850291+00:00
-- url     : https://prove2.me/theorems/2effea07-99f5-4710-b07c-0206f5f1363d
-- title:
--   Theorem 4.2: attained exact SRLS SDP (corrected: τ ≥ 0 for p = 0)
-- statement:
--   Let $A_0,\ldots,A_p\in\mathbb R^{n\times m}$ and $b_0,\ldots,b_p\in\mathbb R^n$ be arbitrary real data. Define $A(\delta)=A_0+\sum_{i=1}^p\delta_iA_i$, $b(\delta)=b_0+\sum_{i=1}^p\delta_ib_i$, and $r_S(x)=\max_{\|\delta\|_2\le1}\|A(\delta)x-b(\delta)\|_2$. A decision is an SRLS solution when it minimizes $r_S$ over all of $\mathbb R^m$. With $a(x)=A_0x-b_0$ and $M(x)=[A_1x-b_1\ \cdots\ A_px-b_p]$, put
--
--   $$
--   B(\lambda,\tau,x)=\begin{bmatrix}\lambda-\tau&0&a(x)^T\\0&\tau I_p&M(x)^T\\a(x)&M(x)&I_n\end{bmatrix},\qquad
--   \operatorname{Feas}(\lambda,\tau,x)\iff\tau\ge0\ \text{and}\ B(\lambda,\tau,x)\succeq0.
--   $$
--
--   An optimal triple is a feasible triple minimizing $\lambda$ among all feasible triples. The complete attained reformulation asserts:
--
--   1. For every $x\in\mathbb R^m$ and $\lambda\in\mathbb R$,
--   $$r_S(x)^2\le\lambda\iff\exists\tau:\operatorname{Feas}(\lambda,\tau,x).$$
--   2. An optimal triple exists for every input data family:
--   $$\exists(\lambda,\tau,x):\operatorname{Opt}(\lambda,\tau,x).$$
--   3. For every triple,
--   $$\operatorname{Opt}(\lambda,\tau,x)\iff\operatorname{Feas}(\lambda,\tau,x)\ \text{and}\ x\in\operatorname*{argmin}_{y\in\mathbb R^m}r_S(y)\ \text{and}\ \lambda=r_S(x)^2.$$
--
--   Consequently every SRLS minimizer has an optimal lift, and the attained SDP value is the square of the attained minimum residual. Singular data, flat directions, and nonunique minimizers are included. No optimal triple or residual minimizer is assumed to exist in the hypotheses.
--
--   **Formalization Note** The explicit $\tau\ge0$ repairs the empty uncertainty dimension. The theorem reuses the original continuous-ball residual and matrix, with unit radius and coefficient exactly 1; $\lambda$ is the squared residual, not the residual.
--
--   Differences from the source:
--   - correction: Eq. (32) imposes only the block PSD constraint → feasibility also requires τ ≥ 0; reason: for p = 0, n = m = 1 and zero data, B = diag(λ − τ, 1); taking τ = λ allows arbitrarily negative λ, whereas the residual is zero; τ ≥ 0 is already implied when p ≥ 1
--   - generalization: the usual positive-dimensional matrix presentation → all natural dimensions n, m, p, including zero, with the stated p = 0 repair; reason: every positive-dimensional instance is retained; n = 0 has zero residual, m = 0 has one decision, and p = 0 is ordinary least squares
--   - encoding: SRLS can be solved by computing an optimal solution of (32) → one statement gives the exact epigraph, existence of an optimal triple, and an iff characterizing all optimal triples; reason: this spells out the attained optimization claim and its solution correspondence; no optimizer is assumed
--   - encoding: real finite-dimensional vectors and the Euclidean unit ball → Fin-indexed real vectors with the published explicit Euclidean norm and residual supremum; reason: zero-based indexing changes no data; the residual image of the continuous compact unit ball is nonempty, bounded, and attains its maximum
-- source:
--   El Ghaoui and Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), https://doi.org/10.1137/S0895479896298130, §4.2 Theorem 4.2, Eq. (32), printed p. 1045 / PDF p. 11; model (2)–(3), printed p. 1036 / PDF p. 2.

import Definitions.Def_RobustLSAudit_Structured_SDP32Feasible
import Theorems.Thm_RobustLS_Structured_sdp32_iff_calF
import Theorems.Thm_RobustLS_Structured_srls_sdp_exact

namespace RobustLSAudit.Structured

/-- Theorem 4.2, Eq. (32), El Ghaoui--Lebret (1997), printed p. 1045 / PDF p. 11:
exact epigraph, unconditional minimum attainment, and both directions of optimal-solution
correspondence for the actual continuous-ball SRLS objective. The explicit `τ ≥ 0` in
`SDP32Feasible` is the minimal repair for `p = 0` (zero data otherwise permit `λ = τ < 0`).
For `p ≥ 1` the feasible set agrees with the printed matrix-only SDP. No rank, consistency,
uniqueness, boundedness of the decision set, or pre-existing optimizer is assumed.
The first and third clauses also imply that every SRLS minimizer has an optimal lift at
`λ = rS ... 1 x ^ 2`; the second clause asserts that such minimizers actually exist. -/
theorem srls_sdp_exact_attained {n m p : ℕ}
    (A0 : Matrix (Fin n) (Fin m) ℝ) (A : Fin p → Matrix (Fin n) (Fin m) ℝ)
    (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) :
    (∀ (x : Fin m → ℝ) (lam : ℝ),
      RobustLS.Structured.rS A0 A b0 b 1 x ^ 2 ≤ lam ↔
        ∃ τ : ℝ, SDP32Feasible A0 A b0 b lam τ x) ∧
    (∃ (lam τ : ℝ) (x : Fin m → ℝ), SDP32Optimal A0 A b0 b lam τ x) ∧
    (∀ (lam τ : ℝ) (x : Fin m → ℝ),
      SDP32Optimal A0 A b0 b lam τ x ↔
        SDP32Feasible A0 A b0 b lam τ x ∧
          RobustLS.Structured.IsSRLSSolution A0 A b0 b 1 x ∧
          lam = RobustLS.Structured.rS A0 A b0 b 1 x ^ 2) := by sorry

end RobustLSAudit.Structured
