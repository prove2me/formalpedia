-- Prove2me | Theorems.Thm_TraceEstimation_Gaussian_upper_tail
-- name    : TraceEstimation.Gaussian.upper_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:29:09.978655+00:00
-- url     : https://prove2.me/theorems/c4ee4bb1-35e1-4713-bb00-31676fd88868
-- title:
--   Section 5, pp. 8:8–8:9 — Chernoff bound $\Pr(G_M \ge \tau(1+\epsilon)) \le e^{-M\epsilon^2/20}$
-- statement:
--   Let $A$ be an $n \times n$ real symmetric positive semi-definite matrix with $\tau = \mathrm{trace}(A) > 0$, let $M \ge 1$ and let $G_M$ be the Gaussian trace estimator with $M$ samples. For every $0 < \epsilon \le 0.1$,
--
--   $$\Pr\bigl(G_M \ge \tau(1+\epsilon)\bigr) \le \exp\!\left(-\frac{M\epsilon^2}{20}\right).$$
--
--   This is the upper-tail bound that the Chernoff-style argument in the proof of Theorem 5.2 establishes; with $M \ge 20\epsilon^{-2}\ln(2/\delta)$ the right-hand side is at most $\delta/2$.
--
--   **Formalization Note** The hypothesis $\tau > 0$ is added: for $A = 0$ the estimator is identically $0 = \tau(1+\epsilon)$ and the event is certain. The paper assumes throughout the proof that it can divide by $\tau$ (in $t_0 = \epsilon/(4\tau(1+\epsilon/2))$). The range $\epsilon \le 0.1$ is the one the page states for the last step of the chain.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), pp. 8:8-8:9, Section 5, proof of Theorem 5.2 (Markov chain of inequalities)

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.Gaussian

open MeasureTheory ProbabilityTheory Matrix

/-- Section 5, pp. 8:8–8:9 (Avron–Toledo), the Chernoff bound in the proof of Theorem 5.2.
For a symmetric positive semi-definite `A` with `τ = trace(A) > 0`, every `M ≥ 1` and every
`0 < ε ≤ 0.1`, `Pr(G_M ≥ τ(1 + ε)) ≤ exp(-M ε² / 20)`. -/
theorem upper_tail {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (htr : 0 < A.trace) (M : ℕ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    (Shared.gaussianSampleMeasure n M).real {ω | A.trace * (1 + ε) ≤ Shared.gaussianEstimator A M ω} ≤
      Real.exp (-(M : ℝ) * ε ^ 2 / 20) := by sorry

end TraceEstimation.Gaussian
