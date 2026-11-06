-- Prove2me | Theorems.Thm_QuerySampleRev_lemma_23
-- name    : QuerySampleRev.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:50.485285+00:00
-- url     : https://prove2.me/theorems/e526ae9a-e2f9-4feb-8cc1-8e8f6bfd3314
-- title:
--   Lemma 23 — $\mathrm{KL}(F^{(0)},F^{(i)})\le AK\varepsilon^2$ with $A=100$
-- statement:
--   Let $c\in[0,1]$, $0<\varepsilon\le1/128$ and $A=100$. For every $i\in[K]$, the Kullback–Leibler divergence of one value sample satisfies
--   $$
--   \mathrm{KL}\big(F^{(0)},F^{(i)}\big)\le AK\varepsilon^2 .
--   $$
--   A value sample is informative about every hard distribution at once; this bound is what makes samples $K$ times more informative than a single query in the tradeoff.
--
--   **Formalization Note** $\mathrm{KL}$ is Mathlib's `InformationTheory.klDiv`, valued in $[0,\infty]$ ($+\infty$ without absolute continuity), as in §2.3.
--
--   Differences from the source: none.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Lemma 23 and the sentence fixing A, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_QuerySampleRev_hardDist

open MeasureTheory InformationTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Lemma 23 (KL Divergence of Samples).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), p.37 (PDF 39): "We fix the absolute constant `A ≜ 100` for
the next two lemmas. … **Lemma 23 (KL Divergence of Samples).** For every `i ∈ [K]`, we have
`KL(F⁽⁰⁾, F⁽ⁱ⁾) ≤ AKε²`."

For `c ∈ [0, 1]`, `0 < ε ≤ 1/128` and `i ∈ [K]`, the Kullback–Leibler divergence of one value sample,
`KL(F⁽⁰⁾, F⁽ⁱ⁾)` (§2.3, p.14, `+∞` without absolute continuity), is at most `100Kε²`.

**Formalization Note.** `KL` is Mathlib's `InformationTheory.klDiv`, valued in `ℝ≥0∞`. -/
theorem lemma_23 {c ε : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / 128) :
    ∀ i ∈ Finset.Icc 1 (numHard ε c),
      klDiv baseDist (hardDist ε c i) ≤ ENNReal.ofReal (100 * (numHard ε c : ℝ) * ε ^ 2) := by sorry

end QuerySampleRev
