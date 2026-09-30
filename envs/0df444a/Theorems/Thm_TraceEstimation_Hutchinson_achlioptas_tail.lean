-- Prove2me | Theorems.Thm_TraceEstimation_Hutchinson_achlioptas_tail
-- name    : TraceEstimation.Hutchinson.achlioptas_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:27:48.038093+00:00
-- url     : https://prove2.me/theorems/e1fa513d-ce71-4cb0-b668-5299da53f49c
-- title:
--   Lemma 7.2 (Achlioptas) — two-sided tail of an average of Rademacher squares $(\alpha^Tz_i)^2$
-- statement:
--   Let $\alpha \in \mathbb{R}^n$ be a unit vector, $\alpha^T\alpha = 1$. Let $z_1, \ldots, z_M \in \mathbb{R}^n$ be independent random vectors whose entries are independent Rademacher random variables ($\Pr(z_{ik} = \pm 1) = 1/2$), and put $Q_i = (\alpha^T z_i)^2$ and
--
--   $$S = \frac{1}{M}\sum_{i=1}^{M} Q_i .$$
--
--   The $Q_i$ are i.i.d. copies of $Q = (\alpha^T z)^2$, with different $z$ but the same $\alpha$, and $\mathrm{E}(Q) = 1$. Then for every $\epsilon > 0$,
--
--   $$\Pr\bigl(|S - 1| \ge \epsilon\bigr) \le 2\exp\left(-\frac{M}{2}\left(\frac{\epsilon^2}{2} - \frac{\epsilon^3}{3}\right)\right).$$
--
--   This is the concentration inequality of Achlioptas (2001, Lemma 5), used in database-friendly random projections. In the analysis of Hutchinson's estimator it is applied to each eigenvector direction of $A$ separately.
--
--   **Formalization Note** The $Q_i$ are constructed as $(\alpha\cdot z_i)^2$ on the product space `hutchinsonSampleMeasure n M` of the sample vectors, not assumed as an abstract i.i.d. sequence with a law hypothesis. The event is $\{\epsilon \le |S - 1|\}$ and the probability is `Measure.real`. $M \ge 1$ is assumed.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:11, Lemma 7.2 (quoted from Achlioptas 2001, Lemma 5)

import Mathlib
import Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator

namespace TraceEstimation.Hutchinson

open MeasureTheory ProbabilityTheory Matrix

/-- Lemma 7.2 (Avron–Toledo, p. 8:11, quoted from Achlioptas 2001, Lemma 5). Let `α ∈ ℝⁿ`
be a unit vector (`αᵀα = 1`), and let `z_1, …, z_M ∈ ℝⁿ` be independent random vectors with
i.i.d. Rademacher entries. With `Q_i = (αᵀ z_i)²` and `S = (1/M) ∑_{i=1}^M Q_i`, for every
`ε > 0`,
`Pr(|S - 1| ≥ ε) ≤ 2 exp(-(M/2)(ε²/2 - ε³/3))`.
The i.i.d. copies `Q_i` are built as `(αᵀ z_i)²` on the product space of the `z_i`. -/
theorem achlioptas_tail {n : ℕ} (α : Fin n → ℝ) (hα : α ⬝ᵥ α = 1) (M : ℕ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 < ε) :
    (hutchinsonSampleMeasure n M).real
        {ω | ε ≤ |(M : ℝ)⁻¹ * ∑ i : Fin M, (α ⬝ᵥ ω i) ^ 2 - 1|} ≤
      2 * Real.exp (-((M : ℝ) / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by sorry

end TraceEstimation.Hutchinson
