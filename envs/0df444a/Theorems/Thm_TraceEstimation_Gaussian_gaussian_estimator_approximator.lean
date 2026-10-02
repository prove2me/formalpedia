-- Prove2me | Theorems.Thm_TraceEstimation_Gaussian_gaussian_estimator_approximator
-- name    : TraceEstimation.Gaussian.gaussian_estimator_approximator
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:30:12.775909+00:00
-- url     : https://prove2.me/theorems/c96a45f3-593a-4785-ae2d-ed3ca0c600a4
-- title:
--   Theorem 5.2 — $G_M$ is an $(\epsilon,\delta)$-approximator for $M \ge 20\epsilon^{-2}\ln(2/\delta)$
-- statement:
--   Let $A$ be an $n \times n$ real symmetric positive semi-definite matrix, let $0 < \epsilon \le 0.1$ and $0 < \delta < 1$. For every natural number $M$ with
--
--   $$M \ge 20\epsilon^{-2}\ln(2/\delta),$$
--
--   the Gaussian trace estimator $G_M = \frac1M\sum_{i=1}^M z_i^TAz_i$, built from $M$ independent vectors with i.i.d. standard normal entries, is an $(\epsilon,\delta)$-approximator of $\mathrm{trace}(A)$:
--
--   $$\Pr\bigl(|G_M - \mathrm{trace}(A)| \le \epsilon\,\mathrm{trace}(A)\bigr) \ge 1-\delta .$$
--
--   The number of samples depends only on $\epsilon$ and $\delta$, not on $n$ or on $A$; this is the Gaussian row of Table I of the paper and the bound against which the other estimators are compared.
--
--   **Formalization Note** The paper prints Theorem 5.2 with no range for $\epsilon$. Its proof bounds the upper tail by $\exp(-M\epsilon^2/20)$ only "for $\epsilon \le 0.1$" (top of p. 8:9), and without a range the printed statement is false: for a rank-one $A$, $\epsilon = 100$ and $\delta = e^{-400}$ it allows $M = 1$, while $\Pr(\chi^2_1 > 101) \approx e^{-50} > \delta$. The statement here is the corrected theorem the proof establishes, with $0 < \epsilon \le 1/10$. The estimator lives on the explicit product Gaussian space of Definition 3.1 and $M \ge 1$ is assumed (it also follows from the threshold).
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:7, Theorem 5.2

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator
import Definitions.Def_TraceEstimation_Shared_IsApproximator

namespace TraceEstimation.Gaussian

open MeasureTheory ProbabilityTheory Matrix

/-- Theorem 5.2 (Avron–Toledo, p. 8:7), in the corrected form its proof establishes.
Let `A` be an `n × n` symmetric positive semi-definite matrix, `0 < ε ≤ 0.1`, `0 < δ < 1`.
For every natural `M ≥ 20 ε⁻² ln(2/δ)`, the Gaussian estimator `G_M` is an
`(ε, δ)`-approximator of `trace(A)`.
The paper prints no range for `ε`; its proof (top of p. 8:9) gives the bound
`exp(-M ε²/20)` only "for ε ≤ 0.1", and without a range the statement is false
(rank-one `A`, `ε = 100`, `δ = e^{-400}` allows `M = 1`). -/
theorem gaussian_estimator_approximator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (ε δ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1)
    (M : ℕ) (hM : 0 < M) (hMbound : 20 * ε⁻¹ ^ 2 * Real.log (2 / δ) ≤ (M : ℝ)) :
    Shared.IsApproximator (Shared.gaussianSampleMeasure n M) (Shared.gaussianEstimator A M) A ε δ := by sorry

end TraceEstimation.Gaussian
