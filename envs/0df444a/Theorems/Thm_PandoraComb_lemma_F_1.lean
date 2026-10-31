-- Prove2me | Theorems.Thm_PandoraComb_lemma_F_1
-- name    : PandoraComb.lemma_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:08:55.177006+00:00
-- url     : https://prove2.me/theorems/791947c1-6e82-4d60-b67e-79eca94b4f6a
-- title:
--   Lemma F.1 — $\lim_{\kappa\to\infty}\mathbb E[(V-\kappa)^+]=0$ for non-negative $V$ with finite mean
-- statement:
--   Let $V$ be a non-negative random variable with finite expectation, with law $\mu$. Then
--
--   $$\lim_{\kappa\to\infty}\mathbb E\big[(V-\kappa)^+\big]=0,\qquad (x)^+=\max(x,0).$$
--
--   This makes the cap $\kappa_\epsilon$ of Transformation $T^\epsilon$ well defined for every $\epsilon>0$.
--
--   Differences from the source:
--   - encoding: a non-negative random variable V with finite expectation → its law μ: a probability measure on ℝ with μ((−∞,0)) = 0 and integrable identity; reason: E[(V − κ)^+] depends only on the law of V
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Lemma F.1, p.35 (proof pp.35–36)

import Mathlib

open MeasureTheory Filter Topology

namespace PandoraComb

/-- **Lemma F.1** (arXiv:2303.01078v1, p.35): "Let V be a non-negative random variable with
finite expectation, then the following holds: lim_{κ→∞} E[(V − κ)^+] = 0."

**Formalization Note.** `V` is given by its law `μ`, a probability measure on `ℝ` with
`μ (−∞, 0) = 0` and finite expectation; `(x)^+ = max x 0`; `κ → ∞` along the reals. -/
theorem lemma_F_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (hint : Integrable (fun x : ℝ => x) μ) :
    Tendsto (fun κ : ℝ => ∫ x, max (x - κ) 0 ∂μ) atTop (𝓝 0) := by sorry

end PandoraComb
