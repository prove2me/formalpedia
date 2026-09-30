-- Prove2me | Theorems.Thm_TraceEstimation_UnitVector_unit_vector_estimator_approximator
-- name    : TraceEstimation.UnitVector.unit_vector_estimator_approximator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:38:52.387722+00:00
-- url     : https://prove2.me/theorems/407fa5dd-cb35-4d7b-88b2-cb31ff89acf2
-- title:
--   Theorem 8.2 — $U_M$ is an $(\epsilon,\delta)$-approximator for $M \ge \frac12\epsilon^{-2}\ln(2/\delta)r_D^2(A)$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ ($n \ge 1$) be symmetric positive semi-definite, let $r_D(A) = n\max_i A_{ii}/\mathrm{trace}(A)$, and let $0 < \epsilon$ and $0 < \delta < 1$. If the number of samples $M \ge 1$ satisfies
--
--   $$M \ge \frac{1}{2}\,\epsilon^{-2}\ln(2/\delta)\,r_D^2(A),$$
--
--   then the unit vector estimator $U_M$ is an $(\epsilon,\delta)$-approximator of $\mathrm{trace}(A)$:
--
--   $$\Pr\bigl(|U_M - \mathrm{trace}(A)| \le \epsilon\,\mathrm{trace}(A)\bigr) \ge 1-\delta .$$
--
--   The bound depends on $A$ only through $r_D(A)$, which is small when the diagonal of $A$ is nearly uniform and as large as $n$ when the trace sits on one diagonal entry.
--
--   **Formalization Note** The sentence of Theorem 8.2 names no hypothesis on $A$; the section's matrix is that of Definition 3.4 (positive definite), and the proof uses that samples lie in $[0, n\max_i A_{ii}]$, i.e. $A_{ii} \ge 0$. The statement is made for positive semi-definite $A$, the weaker hypothesis. No hypothesis $\mathrm{trace}(A) > 0$ is added: for positive semi-definite $A$ with trace $0$, $A = 0$ and the claim holds trivially (Lean's $r_D(0) = 0$).
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:12, Theorem 8.2

import Mathlib
import Definitions.Def_TraceEstimation_Shared_IsApproximator
import Definitions.Def_TraceEstimation_UnitVector_unitVectorEstimator
import Definitions.Def_TraceEstimation_UnitVector_rD

namespace TraceEstimation.UnitVector

open MeasureTheory ProbabilityTheory Matrix Real

/-- Theorem 8.2 (Avron–Toledo, p. 8:12): for a symmetric positive semi-definite `n × n` matrix `A`
(`n ≥ 1`), `0 < ε`, `0 < δ < 1` and `M ≥ 1` samples with
`M ≥ (1/2) ε⁻² ln(2/δ) r_D²(A)`, where `r_D(A) = n · max_i A_ii / trace(A)`, the unit vector
estimator `U_M` is an `(ε, δ)`-approximator of `trace(A)`. -/
theorem unit_vector_estimator_approximator {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (M : ℕ) (hM : 0 < M)
    (hMbound : (1 / 2 : ℝ) * ε⁻¹ ^ 2 * Real.log (2 / δ) * rD A ^ 2 ≤ (M : ℝ)) :
    Shared.IsApproximator (indexSampleMeasure n M) (unitVectorEstimator A M) A ε δ := by sorry

end TraceEstimation.UnitVector
