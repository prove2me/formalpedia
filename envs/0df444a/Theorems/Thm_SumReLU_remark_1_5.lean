-- Prove2me | Theorems.Thm_SumReLU_remark_1_5
-- name    : SumReLU.remark_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:26:36.557981+00:00
-- url     : https://prove2.me/theorems/c91ad231-6202-4249-ade6-6d7adc3f47ff
-- title:
--   Remark 1.5 — $\mathbb E[f(x)]=b/\sqrt{2\pi}$ and $\mathbb E[f(x)^2]\le b^2/2$ for a positive ReLU combination
-- statement:
--   Let $f(x)=\sum_{i=1}^k\beta_i\,\sigma(w_i\cdot x)$ on $\mathbb R^d$ with unit vectors $w_i$ and arbitrary coefficients $\beta_i\ge0$ (no upper bound), and let $b=\sum_{i=1}^k\beta_i$. For $x\sim N(0,I_d)$,
--   $$
--   \mathbb E[f(x)]=\frac{b}{\sqrt{2\pi}},\qquad \mathbb E[f(x)^2]\le\frac{b^2}{2},
--   $$
--   and $f(x)^2$ is integrable.
--
--   These two moments are what the paper's normalization step uses: the mean of the labels estimates the scale $b$, so a learner for coefficients in $[0,1]$ applies to arbitrary positive combinations.
--
--   **Formalization Note** The remark first absorbs the norm of each hidden weight vector into its coefficient; the statement is in that absorbed form.
--
--   Differences from the source:
--   - encoding: arbitrary positive combination, norms absorbed into the coefficients, $b$ the resulting coefficient sum → unit $w_i$, $\beta_i\ge0$, $b=\sum_i\beta_i$; reason: the remark's own reduction by positive homogeneity; a zero weight vector contributes $0$ and can be dropped, so the functions are the same
--   - encoding: $\mathbb E[f(x)^2]\le b^2/2$ → $f^2$ integrable and $\int f^2\,dN\le b^2/2$; reason: the expectation presupposes integrability; asserting it keeps the Bochner integral from being a junk $0$, and $f^2$ is integrable for every such $f$
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Remark 1.5, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_SumReLU_reluSum

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **Remark 1.5** (Normalization), the two moment facts.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Remark 1.5, p.2 (PDF p.4): "Our result applies to arbitrary positive linear combinations of at
most k ReLUs, without bounds on the coefficients or the norms of the hidden weight vectors. By
positive homogeneity, we can absorb the norm of each hidden weight vector into its coefficient.
Writing b for the resulting coefficient sum, we have E[f(x)] = b/√(2π) and E[f(x)²] ≤ b²/2."

**Formalization Note.** After absorbing the norms, `f(x) = ∑_i β_i σ(w_i · x)` with unit `w_i` and
arbitrary `β_i ≥ 0` (no upper bound), and `b = ∑_i β_i`; `x ∼ N(0, I_d)`. The integrability of
`f²` is part of the conclusion. The Chebyshev estimate that follows in the remark is not stated. -/
theorem remark_1_5 {d k : ℕ} (β : Fin k → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (w : Fin k → EuclideanSpace ℝ (Fin d)) (hw : ∀ i, ‖w i‖ = 1) :
    ∫ x, reluSum β w x ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
        (∑ i, β i) / Real.sqrt (2 * Real.pi) ∧
      Integrable (fun x => reluSum β w x ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ x, reluSum β w x ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (∑ i, β i) ^ 2 / 2 := by sorry

end SumReLU
