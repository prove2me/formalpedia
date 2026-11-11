-- Prove2me | Theorems.Thm_ProdMomentConc_lemma_2_3
-- name    : ProdMomentConc.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:09.455877+00:00
-- url     : https://prove2.me/theorems/ff30e69a-6931-4489-bdff-c135cc511cd5
-- title:
--   Lemma 2.3 — exponential product-moment reduction over a random $k$-subset
-- statement:
--   Let $X_1,\dots,X_n$ be real-valued random variables on a probability space and $X := \sum_{i=1}^n X_i$. Let $I$ be a uniformly random $k$-subset of $[n]$, sampled independently of $X_1,\dots,X_n$. Then for every $\alpha \in \mathbb R$, every integer $1 \le k \le n$ and every $\lambda > 0$,
--
--   $$
--   \Pr[X \ge \alpha n] \le e^{-\lambda\alpha k}\, \mathbb E_I\, \mathbb E\Big[\exp\Big(\lambda \sum_{i \in I} X_i\Big)\Big].
--   $$
--
--   This is the exponential form of the paper's basic template: the upper tail of a sum is controlled by the exponential moments of a uniformly random $k$-subset of the summands. Every Chernoff-type bound of the mission is derived from it.
--
--   **Formalization Note** No moment assumption is made, so the exponential moment may be infinite: the right side is a lower Lebesgue integral in $[0,\infty]$, and the probability is the measure of the event in $[0,\infty]$. The expectation over $I$ and the bits is written as an iterated integral (first over the bits for a fixed $S$, then over $S \sim$ `kSubsetLaw n k`), which by Tonelli equals the expectation over the product space. $\lambda$ is called `t`.
--
--   Differences from the source:
--   - encoding: Pr and E of possibly non-integrable exponentials → measure and lower Lebesgue integral in ℝ≥0∞; reason: the source assumes no moments, and this is the reading in which every term is defined (a Bochner integral would be 0 when not integrable)
--   - encoding: I sampled independently of the Xᵢ, E over (I, X) → iterated integral over the bits, then over S ∼ kSubsetLaw n k; reason: Tonelli; the same quantity
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Lemma 2.3, p.9 (PDF p.9)

import Mathlib
import Definitions.Def_ProdMomentConc_kSubsetLaw

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Lemma 2.3 (exponential product-moment reduction).**
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), Lemma 2.3, p.9.

For real random variables `X₁, …, Xₙ`, `X = ∑ Xᵢ`, and `I` a uniformly random `k`-subset of `[n]`
independent of the `Xᵢ`: for every `α ∈ ℝ`, every integer `1 ≤ k ≤ n` and every `λ > 0`,
`Pr[X ≥ αn] ≤ e^{−λαk} E_I E[exp(λ ∑_{i∈I} Xᵢ)]`.

**Formalization Note.** No moment assumption is made on the `Xᵢ`, so the exponential moment may be
`+∞`: the right side is a lower Lebesgue integral in `ℝ≥0∞` and the probability is `μ` of the
event in `ℝ≥0∞`. "Sampled independently" is encoded as the iterated expectation: first over the
bits' space `μ` for a fixed set `S`, then over `S ∼ kSubsetLaw n k` (by Tonelli this is the
expectation over the product space). The parameter `λ` is called `t` (`λ` is reserved in Lean). -/
theorem lemma_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (α : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (t : ℝ) (ht : 0 < t) :
    μ {ω | α * (n : ℝ) ≤ ∑ i, X i ω} ≤
      ENNReal.ofReal (Real.exp (-(t * α * (k : ℝ)))) *
        ∫⁻ S, ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ∑ i ∈ S, X i ω)) ∂μ ∂(kSubsetLaw n k) := by sorry

end ProdMomentConc
