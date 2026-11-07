-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_2_5
-- name    : SoftmaxAttnFD.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:23.945762+00:00
-- url     : https://prove2.me/theorems/fe9a1480-bce8-4571-a46b-31dc9f6bfd8d
-- title:
--   Lemma 2.5, pp.11–12 — perturbation and ratio bounds
-- statement:
--   Let $x,x'\in\mathbb R^n$, $n\ge1$, with $\|x-x'\|_\infty\le\delta$, and let $h=\max_jx_j$, $h'=\max_jx'_j$. Then
--   $$\|\mathrm{softmax}(x)-\mathrm{softmax}(x')\|_1\le2\delta,\qquad|h-h'|\le\delta,$$
--   and for every $j$,
--   $$|(x_j-h)-(x'_j-h')|\le2\delta,\qquad|e^{x_j-h}-e^{x'_j-h'}|\le2\delta.$$
--   Moreover, if $D\ge1$, $|F|\le WD$ and $|\hat D-D|,|\hat F-F|\le\zeta<1$, then
--   $$\Bigl|\frac{\hat F}{\hat D}-\frac FD\Bigr|\le\frac{(W+1)\zeta}{1-\zeta}.$$
--   These bounds transfer errors in scores and in kernel products to the attention output in the final step of the main theorem.
--
--   Differences from the source:
--   - encoding: x, x′ ∈ R^n → n ≥ 1; reason: the maxima need a nonempty index set
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 2.5, pp.11–12

import Definitions.Def_SoftmaxAttnFD_softmax

namespace SoftmaxAttnFD

/-- **Lemma 2.5** (arXiv:2611.06055, sha256 a60f7609…, pp.11–12). Perturbation and ratio bounds.

**Formalization Note** `n ≥ 1` so that the maxima exist; the `⨆` run over the finite nonempty
`Fin n`. The ratio bound is a separate clause on its own real data, as printed. `W` and `ζ` need no
sign hypothesis: `|F| ≤ WD` with `D ≥ 1` gives `W ≥ 0`, and `|D̂ − D| ≤ ζ` gives `ζ ≥ 0`. -/
theorem lemma_2_5 :
    (∀ (n : ℕ) (_ : 1 ≤ n) (x x' : Fin n → ℝ) (δ : ℝ), (∀ j, |x j - x' j| ≤ δ) →
      (∑ j, |softmax x j - softmax x' j| ≤ 2 * δ) ∧
      |(⨆ j, x j) - ⨆ j, x' j| ≤ δ ∧
      (∀ j, |(x j - ⨆ l, x l) - (x' j - ⨆ l, x' l)| ≤ 2 * δ) ∧
      (∀ j, |Real.exp (x j - ⨆ l, x l) - Real.exp (x' j - ⨆ l, x' l)| ≤ 2 * δ)) ∧
    (∀ (D Dh Fv Fh W ζ : ℝ), 1 ≤ D → |Fv| ≤ W * D → |Dh - D| ≤ ζ → |Fh - Fv| ≤ ζ → ζ < 1 →
      |Fh / Dh - Fv / D| ≤ (W + 1) * ζ / (1 - ζ)) := by sorry

end SoftmaxAttnFD
