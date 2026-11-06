-- Prove2me | Theorems.Thm_QuerySampleRev_lemma_24
-- name    : QuerySampleRev.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:58.094825+00:00
-- url     : https://prove2.me/theorems/7a8ad57c-a48f-41c7-b758-746747019ab6
-- title:
--   Lemma 24 — $\mathrm{KL}(F^{(0)}(p),F^{(i)}(p))\le A\varepsilon^2$ for $p\in P^{(i)}$
-- statement:
--   Let $c\in[0,1]$, $0<\varepsilon\le1/128$ and $A=100$. For every $i\in[K]$ and every query price $p\in P^{(i)}$,
--   $$
--   \mathrm{KL}\big(F^{(0)}(p),F^{(i)}(p)\big)=\mathrm{KL}\big(Q^{(0)}(p),Q^{(i)}(p)\big)\le A\varepsilon^2 ,
--   $$
--   the Bernoulli KL divergence between the laws of the query feedback $\mathbf 1[v\ge p]$ under $F^{(0)}$ and $F^{(i)}$.
--
--   A pricing query is informative only about the hard distribution whose interval contains its price, and then only by $O(\varepsilon^2)$.
--
--   **Formalization Note** The binary KL is `ExploreFirst.FundIneq.klBer` applied to the real sale probabilities $Q(p)=\mu([p,\infty))$.
--
--   Differences from the source: none.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Lemma 24, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting
import Definitions.Def_QuerySampleRev_rStar
import Definitions.Def_QuerySampleRev_hardDist

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Lemma 24 (KL Divergence of Queries).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), p.38 (PDF 40): "For every `i ∈ [K]` and every query price
`p ∈ P⁽ⁱ⁾`, we have `KL(F⁽⁰⁾(p), F⁽ⁱ⁾(p)) ≤ Aε²`", with `A ≜ 100` (p.37).

`KL(F⁽⁰⁾(p), F⁽ⁱ⁾(p))` is the divergence between the feedback laws `1[v ≥ p]` at price `p`, i.e. the
Bernoulli KL `KL(Q⁽⁰⁾(p), Q⁽ⁱ⁾(p))` (§2.3, p.14).

**Formalization Note.** The binary KL is the published `ExploreFirst.FundIneq.klBer` (the `klDiv` of the
two Bernoulli laws, in `ℝ≥0∞`); the sale probabilities `Q(p) = μ([p, ∞))` enter as real numbers. -/
theorem lemma_24 {c ε : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / 128) :
    ∀ i ∈ Finset.Icc 1 (numHard ε c), ∀ p ∈ priceInterval ε c i,
      ExploreFirst.FundIneq.klBer (saleProb baseDist p).toReal (saleProb (hardDist ε c i) p).toReal ≤
        ENNReal.ofReal (100 * ε ^ 2) := by sorry

end QuerySampleRev
