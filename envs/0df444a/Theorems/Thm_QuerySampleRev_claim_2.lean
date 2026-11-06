-- Prove2me | Theorems.Thm_QuerySampleRev_claim_2
-- name    : QuerySampleRev.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:57.142763+00:00
-- url     : https://prove2.me/theorems/bb462c9c-3f53-4a06-8edf-0620c7c130a9
-- title:
--   Claim 2 — KL of a transcript event $\le\mathbb E_{F^{(0)}}[S]\,\mathrm{KL}(F^{(0)},F^{(i)})+\mathbb E_{F^{(0)}}[Q^{(i)}]\sup_{P^{(i)}}\mathrm{KL}$
-- statement:
--   Let $F^{(0)}$ and $F^{(i)}$ be value distributions on $[0,\infty)$ that agree outside a measurable price set $P^{(i)}\subseteq[0,\infty)$, in the sense that their left-continuous CDFs satisfy
--   $$
--   F^{(0)}(p)=F^{(i)}(p)\qquad\text{for every }p\notin P^{(i)} .
--   $$
--   Let $A$ be any learning algorithm, $S$ its number of value samples and $Q^{(i)}$ its number of pricing queries with price in $P^{(i)}$. Then for every measurable transcript event $\mathcal E$,
--   $$
--   \mathrm{KL}\big(\mathbb P_{F^{(0)}}[\mathcal E],\mathbb P_{F^{(i)}}[\mathcal E]\big)\le\mathbb E_{F^{(0)}}[S]\,\mathrm{KL}(F^{(0)},F^{(i)})+\mathbb E_{F^{(0)}}[Q^{(i)}]\sup_{p\in P^{(i)}}\mathrm{KL}\big(F^{(0)}(p),F^{(i)}(p)\big).
--   $$
--   Here the left side is the Bernoulli KL divergence of the two event probabilities, $\mathrm{KL}(F^{(0)},F^{(i)})$ is the KL divergence of one value sample, and $\mathrm{KL}(F^{(0)}(p),F^{(i)}(p))=\mathrm{KL}(Q^{(0)}(p),Q^{(i)}(p))$ is the Bernoulli KL divergence of the query feedback at price $p$.
--
--   This is the divergence decomposition behind all lower bounds of the paper: queries outside the modified price set carry no information about which of the two distributions generated the data.
--
--   **Formalization Note** The binary KL is the published `ExploreFirst.FundIneq.klBer`; all divergences, expectations and the supremum are in $[0,\infty]$ with $0\cdot\infty=0$.
--
--   Differences from the source:
--   - generalization: the learner terminates almost surely under both distributions → no termination hypothesis; $S$ and $Q^{(i)}$ count the rounds before the possibly infinite stopping time; reason: the bound holds for every finite prefix of the run and passes to the limit; specializes to the source for learners that terminate almost surely
--   - generalization: transcript events (access types, samples, prices, feedback, output) → events of the transcript that also records the internal seed; reason: a finer σ-algebra: every event of the source's transcript is such an event
--   - generalization: learners choose query prices $p_t\ge0$ → learners may query and output any real price; reason: a larger class of learners; a query at $p\le0$ is answered $1$ almost surely, so the class contains every learner of §2.2
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: expectations of the counts $S$, $T$ → lower Lebesgue integrals of $\mathbb N\cup\{\infty\}$-valued counts, in $[0,\infty]$; reason: no integrability condition is needed; the value is $+\infty$ when the expectation is infinite
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Claim 2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting
import Definitions.Def_QuerySampleRev_rStar
import Definitions.Def_QuerySampleRev_transcript
import Definitions.Def_QuerySampleRev_lawP

open MeasureTheory InformationTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Claim 2 (Learning Algorithms).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), Claim 2, p.14 (PDF 16): "Two value distributions `F⁽⁰⁾` and
`F⁽ⁱ⁾` agree outside a measurable price set `P⁽ⁱ⁾ ⊆ [0, ∞)`, so that `F⁽⁰⁾(p) = F⁽ⁱ⁾(p)` for every
`p ∉ P⁽ⁱ⁾`. A learning algorithm `A` terminates almost surely under both distributions. We denote its
sample count by `S` and the number of its queries with prices in `P⁽ⁱ⁾` by `Q⁽ⁱ⁾`. For every measurable
transcript event `𝓔`, the induced transcript laws satisfy
`KL(P_{F⁽⁰⁾}[𝓔], P_{F⁽ⁱ⁾}[𝓔]) ≤ E_{F⁽⁰⁾}[S] KL(F⁽⁰⁾, F⁽ⁱ⁾) + E_{F⁽⁰⁾}[Q⁽ⁱ⁾] sup_{p∈P⁽ⁱ⁾} KL(F⁽⁰⁾(p), F⁽ⁱ⁾(p))`."

For value distributions `μ₀, μ₁` (probability measures on `[0, ∞)`) whose left-continuous CDFs agree
outside a measurable set `P ⊆ [0, ∞)`, every learner `L` and every measurable set `A` of transcripts,
with `𝓔 = {transcript ∈ A}`.

**Formalization Note.** The almost-sure termination hypothesis is not assumed: `S` and `Q⁽ⁱ⁾` count the
rounds before the (possibly infinite) stopping time, in `ℕ∞`, and expectations are lower Lebesgue
integrals in `ℝ≥0∞`. The transcript includes the seed (a finer σ-algebra). Binary KL is
`ExploreFirst.FundIneq.klBer`; KL of value laws is `InformationTheory.klDiv`. -/
theorem claim_2 (μ₀ μ₁ : Measure ℝ) (hμ₀ : IsProbabilityMeasure μ₀) (hμ₁ : IsProbabilityMeasure μ₁)
    (hμ₀0 : μ₀ (Set.Iio 0) = 0) (hμ₁0 : μ₁ (Set.Iio 0) = 0)
    (P : Set ℝ) (hP : MeasurableSet P) (hP0 : P ⊆ Set.Ici 0)
    (hagree : ∀ p ∉ P, cdf μ₀ p = cdf μ₁ p)
    (L : Learner) (A : Set (unitInterval × (ℕ → Obs ⊕ Unit))) (hA : MeasurableSet A) :
    ExploreFirst.FundIneq.klBer (lawP μ₀ (transcript L ⁻¹' A)).toReal
        (lawP μ₁ (transcript L ⁻¹' A)).toReal ≤
      (∫⁻ ω, (sampleCount L ω : ℝ≥0∞) ∂lawP μ₀) * klDiv μ₀ μ₁ +
        (∫⁻ ω, (queryCountIn L P ω : ℝ≥0∞) ∂lawP μ₀) *
          ⨆ p ∈ P, ExploreFirst.FundIneq.klBer (saleProb μ₀ p).toReal (saleProb μ₁ p).toReal := by sorry

end QuerySampleRev
