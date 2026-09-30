-- Prove2me | Theorems.Thm_TraceEstimation_Hutchinson_hutchinson_estimator_approximator
-- name    : TraceEstimation.Hutchinson.hutchinson_estimator_approximator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:32:52.116466+00:00
-- url     : https://prove2.me/theorems/98e52f68-4c39-4dca-a273-2f4331e260e2
-- title:
--   Theorem 7.1 — $H_M$ is an $(\epsilon,\delta)$-approximator for $M \ge 6\epsilon^{-2}\ln(2\,\mathrm{rank}(A)/\delta)$, $0<\epsilon\le 1/2$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be symmetric positive semi-definite, let $0 < \epsilon \le 1/2$ and $0 < \delta < 1$, and let $H_M = \frac1M\sum_{i=1}^M z_i^TAz_i$ be Hutchinson's trace estimator with $M \ge 1$ samples, the $z_i$ independent random vectors with independent Rademacher entries. If
--
--   $$M \ge 6\epsilon^{-2}\ln\!\left(\frac{2\,\mathrm{rank}(A)}{\delta}\right),$$
--
--   then $H_M$ is an $(\epsilon,\delta)$-approximator of $\mathrm{trace}(A)$:
--
--   $$\Pr\bigl(|H_M - \mathrm{trace}(A)| \le \epsilon\,\mathrm{trace}(A)\bigr) \ge 1 - \delta .$$
--
--   This is the first sample-complexity bound for Hutchinson's method, the most widely used randomized trace estimator. It exceeds the Gaussian estimator's bound by a $\ln(\mathrm{rank}(A))$ factor, which the authors conjecture is not needed.
--
--   **Formalization Note** The paper prints the theorem with no range on $\epsilon$. Its proof (p. 8:11) passes from Lemma 7.2 to the bound $\delta/\mathrm{rank}(A)$ using $\frac{M}{2}(\frac{\epsilon^2}{2} - \frac{\epsilon^3}{3}) \ge \frac{M\epsilon^2}{6}$, which requires $\epsilon \le 1/2$, and without a range the printed statement is false: for $A = \frac1n\mathbf 1\mathbf 1^T$ (rank $1$, trace $1$), $n = 10^4$, $\epsilon = 10$, $\delta = 10^{-4}$, the condition admits $M = 1$, while $\Pr(H_1 > 11) \approx 9\cdot 10^{-4} > \delta$. The theorem is therefore stated for $0 < \epsilon \le 1/2$. $\mathrm{rank}(A)$ is `Matrix.rank`. For $A = 0$, Lean's convention $\ln 0 = 0$ makes the condition $M \ge 0$, in agreement with the paper's $\ln 0 = -\infty$; the conclusion then holds because $H_M = \mathrm{trace}(A) = 0$. The sample space is `hutchinsonSampleMeasure n M` and the approximator predicate is Definition 4.1.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:10, Theorem 7.1 (proof p. 8:11)

import Mathlib
import Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator
import Definitions.Def_TraceEstimation_Shared_IsApproximator

namespace TraceEstimation.Hutchinson

open MeasureTheory ProbabilityTheory Matrix

/-- Theorem 7.1 (Avron–Toledo, p. 8:10; proof p. 8:11), in the corrected form its proof
establishes. Let `A` be an `n × n` symmetric positive semi-definite matrix, `0 < ε ≤ 1/2`,
`0 < δ < 1`. For every natural `M ≥ 1` with `M ≥ 6 ε⁻² ln(2 rank(A)/δ)`, Hutchinson's
estimator `H_M` is an `(ε, δ)`-approximator of `trace(A)`.
The paper prints no range for `ε`; its proof (p. 8:11) needs `ε ≤ 1/2`, and without a range
the statement is false (`A = (1/n) 𝟙𝟙ᵀ`, `n = 10⁴`, `ε = 10`, `δ = 10⁻⁴` allows `M = 1`,
while `Pr(H_1 > 11) ≈ 9·10⁻⁴ > δ`).
For `A = 0` (rank `0`) Lean's `Real.log 0 = 0` makes the sample condition `M ≥ 0`, matching
the paper's `ln 0 = -∞`; the conclusion then holds because `H_M = trace(A) = 0`. -/
theorem hutchinson_estimator_approximator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (ε δ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 < δ) (hδ' : δ < 1)
    (M : ℕ) (hM : 0 < M) (hMbound : 6 * ε⁻¹ ^ 2 * Real.log (2 * (A.rank : ℝ) / δ) ≤ (M : ℝ)) :
    Shared.IsApproximator (hutchinsonSampleMeasure n M) (hutchinsonEstimator A M) A ε δ := by sorry

end TraceEstimation.Hutchinson
