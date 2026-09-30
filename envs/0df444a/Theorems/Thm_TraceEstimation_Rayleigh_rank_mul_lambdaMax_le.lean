-- Prove2me | Theorems.Thm_TraceEstimation_Rayleigh_rank_mul_lambdaMax_le
-- name    : TraceEstimation.Rayleigh.rank_mul_lambdaMax_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:20:23.627739+00:00
-- url     : https://prove2.me/theorems/c9c30ec2-2f78-4491-b3b6-44ba6545fcc5
-- title:
--   Theorem 6.1, proof — $\mathrm{trace}(A)\,\kappa_f(A) \ge \mathrm{rank}(A)\,\lambda_n$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a nonzero symmetric positive semi-definite matrix, let $\lambda_n$ be its largest eigenvalue, and let $\kappa_f(A)$ be the ratio between its largest and smallest nonzero eigenvalue. Then
--
--   $$\mathrm{trace}(A)\cdot\kappa_f(A) \;\ge\; \mathrm{rank}(A)\,\lambda_n .$$
--
--   This linear-algebra inequality converts the largest eigenvalue, which bounds a single sample $z^TAz$, into a multiple of the trace, so that the range of each sample is measured relative to the quantity being estimated.
--
--   **Formalization Note** The page derives the inequality from an indexing $0 = \lambda_1 = \cdots = \lambda_k \le \cdots \le \lambda_n$ with $k = n - \mathrm{rank}(A) + 1$ and writes $\kappa_f(A) = \lambda_n/\lambda_k$; with that $k$, $\lambda_k = 0$, whereas $\kappa_f$ needs $\lambda_k$ to be the smallest nonzero eigenvalue (an off-by-one slip). Only the inequality is stated, with $\kappa_f$ as defined in `kappaF`. The hypothesis $A \ne 0$ excludes the placeholder value of $\kappa_f(0)$.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:10, Section 6, proof of Theorem 6.1, display 1

import Mathlib
import Definitions.Def_TraceEstimation_Rayleigh_kappaF

namespace TraceEstimation.Rayleigh

open Matrix

/-- Avron–Toledo, proof of Theorem 6.1 (p. 8:10), first display: for a symmetric positive
semi-definite `A ≠ 0` with largest eigenvalue `λ_n` and `κ_f(A)` the ratio of its largest to its
smallest nonzero eigenvalue,
`trace(A) · κ_f(A) ≥ rank(A) · λ_n`.
(The page indexes the eigenvalues as `0 = λ_1 = ⋯ = λ_k ≤ ⋯ ≤ λ_n` with `k = n − rank(A) + 1`,
which makes `λ_k = 0`; the intended `λ_k` is the smallest nonzero eigenvalue. Only the
inequality is stated.) -/
theorem rank_mul_lambdaMax_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hA0 : A ≠ 0) :
    (A.rank : ℝ) * lambdaMax hA.isHermitian ≤ A.trace * kappaF hA.isHermitian := by sorry

end TraceEstimation.Rayleigh
