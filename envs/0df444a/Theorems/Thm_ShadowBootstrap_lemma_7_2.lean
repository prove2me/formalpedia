-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_7_2
-- name    : ShadowBootstrap.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:58.359389+00:00
-- url     : https://prove2.me/theorems/8a236df8-11dd-4b13-a573-23a2e645768e
-- title:
--   Lemma 7.2 — confidence amplification: $O(\log(1/\delta))$ runs and selection give $\Pr[D(\hat X, x_\star) \le 3r] \ge 1 - \delta$
-- statement:
--   There is an absolute constant $c$ with the following property. Let $(X, D)$ be a pseudometric space with a σ-algebra containing the open sets, $x_\star \in X$, $r \in \mathbb R$, and $\mu$ the output law of an estimator with
--   $$\Pr_{X\sim\mu}[D(X, x_\star) \le r] \ge 2/3 .$$
--   For every $0 < \delta < 1/2$ and every number of independent runs $R + 1 \ge c\log(1/\delta)$, the output $\hat X$ selected by pairwise distances (the first run with more than half of all runs within $2r$) satisfies
--   $$\Pr\big[D(\hat X, x_\star) > 3r\big] \le \delta,\qquad\text{i.e.}\qquad \Pr\big[D(\hat X, x_\star) \le 3r\big] \ge 1 - \delta .$$
--
--   Theorem 7.3 applies it with the trace distance between pure states.
--
--   Differences from the source:
--   - generalization: a metric space → a pseudometric space with a σ-algebra containing the open sets and any probability measure as the output law; reason: every metric space with its Borel σ-algebra is one; the trace distance on unit vectors is only a pseudometric
--   - generalization: selecting one output using pairwise distances → the specific rule select (first output with more than half of all outputs within 2r); reason: a specific rule with the guarantee implies the printed statement
--   - reading: running A independently O(log(1/δ)) times → R + 1 independent runs (product measure) for every R with R + 1 ≥ c·log(1/δ), c absolute; reason: O(·) with a universal constant
--   - encoding: Pr[D(X̂, x⋆) ≤ 3r] ≥ 1 − δ → the failure event has (outer) measure ≤ δ; reason: equivalent for a measurable selection and needs no measurability of select
--   - reading: with efficiently computable distances → not stated; reason: it plays no role in the probability claim; Theorem 7.3 pays for the distances in its time bound
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 7.2, p.28 (cited from [HKOT23, Proposition 2.4])

import Mathlib
import Definitions.Def_ShadowBootstrap_select

open MeasureTheory

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 7.2, p.28 (confidence amplification, [HKOT23, Proposition 2.4]): let `A` estimate an
unknown point `x⋆` of a metric space `(X, D)` with output `X` satisfying `Pr[D(X, x⋆) ≤ r] ≥ 2/3`.
For any `0 < δ < 1/2`, running `A` independently `O(log(1/δ))` times and selecting one output using
pairwise distances yields `X̂` with `Pr[D(X̂, x⋆) ≤ 3r] ≥ 1 − δ`.

**Formalization Note** `A`'s output law is any probability measure `μ` on a pseudometric space
with a Borel-compatible σ-algebra; the runs are `R + 1` independent copies (`Measure.pi`) with
`R + 1 ≥ c log(1/δ)` for one absolute constant `c`; the selection rule is `select` (the first output
with more than half of all outputs within `2r`). The conclusion is stated through the failure event,
`Pr[D(X̂, x⋆) > 3r] ≤ δ` (an outer-measure bound, so no measurability of the selection is needed),
which gives the printed bound. A pseudometric covers the trace distance on unit vectors used in
Theorem 7.3. -/
theorem lemma_7_2 :
    ∃ c : ℝ, ∀ (X : Type) [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
      (μ : Measure X) [IsProbabilityMeasure μ] (xstar : X) (r : ℝ),
      (2 / 3 : ENNReal) ≤ μ (Metric.closedBall xstar r) →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ R : ℕ, c * Real.log (1 / δ) ≤ (R : ℝ) + 1 →
        Measure.pi (fun _ : Fin (R + 1) => μ) {v | 3 * r < dist (select r v) xstar}
          ≤ ENNReal.ofReal δ := by sorry

end ShadowBootstrap
