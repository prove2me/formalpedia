-- Prove2me | Theorems.Thm_QuerySampleRev_lemma_10
-- name    : QuerySampleRev.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:42.738299+00:00
-- url     : https://prove2.me/theorems/f980e9bd-518d-42c8-ac0a-0541bff79f82
-- title:
--   Lemma 10 — $\sum_i w_i(d_i\mathbb E_{F^{(0)}}[S]+b_i\mathbb E_{F^{(0)}}[T^{(i)}])\ge\frac W{16}\log\frac1\delta$
-- statement:
--   Let $F^{(0)}$ be a base value distribution and $F^{(i)}$, $i\in I$, alternative value distributions indexed by a finite set $I$, all on $[0,\infty)$, where $F^{(i)}$ agrees with $F^{(0)}$ (equal left-continuous CDFs) outside a price set $P^{(i)}$. Suppose that
--   $$
--   \mathrm{KL}(F^{(0)},F^{(i)})\le d_i\qquad\text{and}\qquad \mathrm{KL}\big(F^{(0)}(p),F^{(i)}(p)\big)\le b_i\ \text{ for every }p\in P^{(i)}.
--   $$
--   For a learning algorithm let $S$ be its number of value samples and $T^{(i)}$ its number of pricing queries with price in $P^{(i)}$. Let $\mathcal E^{(i)}$ be transcript events with $\mathbb P_{F^{(i)}}[\mathcal E^{(i)}]\ge1-\delta$ for every $i\in I$, where $0<\delta\le1/4$, and let $w_i>0$ be weights with sum $W=\sum_{i\in I}w_i$. If $\sum_{i\in I}w_i\,\mathbb P_{F^{(0)}}[\mathcal E^{(i)}]\le W/2$, then
--   $$
--   \sum_{i\in I}w_i\Big(d_i\,\mathbb E_{F^{(0)}}[S]+b_i\,\mathbb E_{F^{(0)}}[T^{(i)}]\Big)\ \ge\ \frac W{16}\log\frac1\delta. \tag{1}
--   $$
--   An algorithm whose output identifies each alternative must therefore collect, on weighted average, KL divergence at least $\tfrac1{16}\log\tfrac1\delta$ from its samples and queries. The paper applies it with equal weights in the quasi-MHR lower bound (Theorem 21) and with weights $1/i$ in the quasi-regular one.
--
--   **Formalization Note** $d_i,b_i$, the divergences and the expectations are in $[0,\infty]$; the event condition is $\mathbb P_{F^{(i)}}[\mathcal E^{(i)}]\ge\mathrm{ofReal}(1-\delta)$.
--
--   Differences from the source:
--   - generalization: price intervals $P^{(i)}$ → measurable price sets $P^{(i)}\subseteq[0,\infty)$; reason: intervals in $[0,\infty)$ are such sets; this is the generality of Claim 2
--   - generalization: output events $\mathcal E^{(i)}$ → measurable transcript events (the transcript includes the internal seed); reason: the output is a function of the transcript, so every output event is a transcript event
--   - encoding: counts of the algorithm, with no termination assumption stated → $\mathbb N\cup\{\infty\}$-valued counts of the rounds before the possibly infinite stopping time; reason: finite counts are unchanged; a non-stopping run is covered
--   - encoding: $d_i$, $b_i$ real bounds → $d_i,b_i\in[0,\infty]$; reason: real nonnegative bounds are a special case; KL values are in $[0,\infty]$
--   - generalization: learners choose query prices $p_t\ge0$ → learners may query and output any real price; reason: a larger class of learners; a query at $p\le0$ is answered $1$ almost surely, so the class contains every learner of §2.2
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: expectations of the counts $S$, $T$ → lower Lebesgue integrals of $\mathbb N\cup\{\infty\}$-valued counts, in $[0,\infty]$; reason: no integrability condition is needed; the value is $+\infty$ when the expectation is infinite
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Lemma 10, p.23 (PDF p.25), display (1)

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting
import Definitions.Def_QuerySampleRev_rStar
import Definitions.Def_QuerySampleRev_transcript
import Definitions.Def_QuerySampleRev_lawP

open MeasureTheory InformationTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Lemma 10.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript,
sha256 c31ea3d3…), Lemma 10, p.23 (PDF 25): "Consider a base distribution `F⁽⁰⁾` and alternative
distributions `F⁽ⁱ⁾` indexed by a finite set `I`, where each `F⁽ⁱ⁾` agrees with `F⁽⁰⁾` outside a price
interval `P⁽ⁱ⁾`. Suppose that `KL(F⁽⁰⁾, F⁽ⁱ⁾) ≤ d_i` and that `KL(F⁽⁰⁾(p), F⁽ⁱ⁾(p)) ≤ b_i` for every
`p ∈ P⁽ⁱ⁾`. … Suppose that output events `𝓔⁽ⁱ⁾` satisfy `P_{F⁽ⁱ⁾}[𝓔⁽ⁱ⁾] ≥ 1 − δ` for every `i ∈ I`, where
`0 < δ ≤ 1/4`. Let `{w_i}_{i∈I}` be positive weights with sum `W ≜ ∑_{i∈I} w_i`. If
`∑_{i∈I} w_i P_{F⁽⁰⁾}[𝓔⁽ⁱ⁾] ≤ W/2`, then
`∑_{i∈I} w_i (d_i E_{F⁽⁰⁾}[S] + b_i E_{F⁽⁰⁾}[T⁽ⁱ⁾]) ≥ (W/16) log(1/δ)`. (1)"

Value distributions are probability measures on `[0, ∞)`; "agrees outside `P⁽ⁱ⁾`" is equality of the
left-continuous CDFs at every `p ∉ P⁽ⁱ⁾`; the event `𝓔⁽ⁱ⁾` is `{transcript ∈ A i}`.

**Formalization Note.** The price intervals are generalized to measurable price sets `P⁽ⁱ⁾ ⊆ [0, ∞)` and
output events to transcript events (the output is a function of the transcript). No termination is
assumed; counts are in `ℕ∞` and expectations are lower integrals in `ℝ≥0∞`, as are `d_i`, `b_i`. -/
theorem lemma_10 {ι : Type*} [Fintype ι] (μ₀ : Measure ℝ) (μ : ι → Measure ℝ)
    (hμ₀ : IsProbabilityMeasure μ₀) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ₀0 : μ₀ (Set.Iio 0) = 0) (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (P : ι → Set ℝ) (hP : ∀ i, MeasurableSet (P i)) (hP0 : ∀ i, P i ⊆ Set.Ici 0)
    (hagree : ∀ i, ∀ p ∉ P i, cdf μ₀ p = cdf (μ i) p)
    (d b : ι → ℝ≥0∞) (hd : ∀ i, klDiv μ₀ (μ i) ≤ d i)
    (hb : ∀ i, ∀ p ∈ P i,
      ExploreFirst.FundIneq.klBer (saleProb μ₀ p).toReal (saleProb (μ i) p).toReal ≤ b i)
    (L : Learner) (A : ι → Set (unitInterval × (ℕ → Obs ⊕ Unit))) (hA : ∀ i, MeasurableSet (A i))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hsucc : ∀ i, ENNReal.ofReal (1 - δ) ≤ lawP (μ i) (transcript L ⁻¹' A i))
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hbase : ∑ i, w i * (lawP μ₀ (transcript L ⁻¹' A i)).toReal ≤ (∑ i, w i) / 2) :
    ENNReal.ofReal ((∑ i, w i) / 16 * Real.log (1 / δ)) ≤
      ∑ i, ENNReal.ofReal (w i) *
        (d i * ∫⁻ ω, (sampleCount L ω : ℝ≥0∞) ∂lawP μ₀ +
          b i * ∫⁻ ω, (queryCountIn L (P i) ω : ℝ≥0∞) ∂lawP μ₀) := by sorry

end QuerySampleRev
