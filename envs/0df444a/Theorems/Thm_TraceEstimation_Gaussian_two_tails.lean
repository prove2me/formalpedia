-- Prove2me | Theorems.Thm_TraceEstimation_Gaussian_two_tails
-- name    : TraceEstimation.Gaussian.two_tails
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:29:29.62784+00:00
-- url     : https://prove2.me/theorems/bc380fdc-498e-44d8-9422-3e056a90eb1e
-- title:
--   Section 5, p. 8:9 — both tails of $G_M$ are at most $\delta/2$
-- statement:
--   Let $A$ be an $n \times n$ real symmetric positive semi-definite matrix with $\tau = \mathrm{trace}(A) > 0$, let $0 < \epsilon \le 0.1$ and $0 < \delta < 1$, and let $M$ be a natural number with
--
--   $$M \ge 20\epsilon^{-2}\ln(2/\delta).$$
--
--   Then the Gaussian trace estimator $G_M$ satisfies
--
--   1. $\Pr\bigl(G_M \ge \tau(1+\epsilon)\bigr) \le \delta/2$, and
--   2. $\Pr\bigl(G_M \le \tau(1-\epsilon)\bigr) \le \delta/2$.
--
--   These are the two one-sided bounds that, combined with a union bound, give Theorem 5.2.
--
--   **Formalization Note** The closing sentence of the paper's proof reads "if $M \ge 20\epsilon^{-2}\ln(2/\delta)$ then $\Pr(G_M \le \tau(1+\epsilon)) \le \delta/2$. Using the same technique, a lower bound can be shown". The first inequality is a misprint for the upper tail $\Pr(G_M \ge \tau(1+\epsilon)) \le \delta/2$, which is part 1; the lower bound the page announces without a constant is stated in part 2 with the same threshold on $M$, which is what the union bound requires. The hypothesis $\tau > 0$ excludes $A = 0$, for which both events are certain.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:9, Section 5, end of the proof of Theorem 5.2

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.Gaussian

open MeasureTheory ProbabilityTheory Matrix

/-- Section 5, p. 8:9 (Avron–Toledo), the closing sentence of the proof of Theorem 5.2, with
its two misprints corrected. For a symmetric positive semi-definite `A` with
`τ = trace(A) > 0`, `0 < ε ≤ 0.1`, `0 < δ < 1` and `M ≥ 20 ε⁻² ln(2/δ)`:
`Pr(G_M ≥ τ(1 + ε)) ≤ δ/2` (the upper tail) and `Pr(G_M ≤ τ(1 - ε)) ≤ δ/2` (the lower tail,
"shown using the same technique"). The page prints `Pr(G_M ≤ τ(1+ε)) ≤ δ/2` for the first. -/
theorem two_tails {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (htr : 0 < A.trace) (ε δ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1)
    (M : ℕ) (hM : 0 < M) (hMbound : 20 * ε⁻¹ ^ 2 * Real.log (2 / δ) ≤ (M : ℝ)) :
    (Shared.gaussianSampleMeasure n M).real {ω | A.trace * (1 + ε) ≤ Shared.gaussianEstimator A M ω} ≤
      δ / 2 ∧
    (Shared.gaussianSampleMeasure n M).real {ω | Shared.gaussianEstimator A M ω ≤ A.trace * (1 - ε)} ≤
      δ / 2 := by sorry

end TraceEstimation.Gaussian
