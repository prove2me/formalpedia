-- Prove2me | Theorems.Thm_QMCBeyondHK_proposition_2_4
-- name    : QMCBeyondHK.proposition_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:15.414676+00:00
-- url     : https://prove2.me/theorems/1f8fe446-d3cb-40b7-a9b3-61f2eb304934
-- title:
--   Proposition 2.4 — a $(1+\varepsilon)$-online thinning strategy uses more than $(1+2\varepsilon)n$ samples (more than $(1+\varepsilon)n$ when $\int\mu_t = 1$) with probability $\le e^{-c\varepsilon n}$
-- statement:
--   There is an absolute constant $c > 0$ with the following property. Let $d \ge 1$, $\varepsilon \in (0,1)$, $n \ge 1$, let $(x_t,\xi_t,y_t)$ be an independent uniform input stream, and let $(\mu_t)$ be any target-density rule of the $(1+\varepsilon)$-online thinning framework. In its first $n$ steps the strategy consumes $n + R_n$ samples, where $R_n$ is the number of steps $t < n$ that reject $x_t$ and draw $y_t$. Then
--   $$
--   \mathbb P\big(n + R_n > (1+2\varepsilon) n\big) \le e^{-c\,\varepsilon n}
--   $$
--   for every rule whose densities are determined measurably by the earlier steps and take values in $[1-\varepsilon/2, 1+\varepsilon/2]$ on $[0,1)^d$, and
--   $$
--   \mathbb P\big(n + R_n > (1+\varepsilon) n\big) \le e^{-c\,\varepsilon n}
--   $$
--   when, in addition, every $\mu_t$ is a probability density ($\int_{[0,1)^d} \mu_t = 1$).
--
--   So with high probability every such strategy gets by with $(1+2\varepsilon)n$ samples, and every strategy with probability densities, Haar-thinning included, with $(1+\varepsilon)n$.
--
--   Differences from the source:
--   - generalization: with high probability at most (1 + O(ε))n samples → for an absolute c > 0, P(more than (1 + 2ε)n samples) ≤ exp(−cεn) for every strategy, and P(more than (1 + ε)n samples) ≤ exp(−cεn) when ∫ μ_t = 1; reason: explicit instances of O(ε) and of 'with high probability' (the paper's proof gives exp(−Ω(εn)) for (1 + 2ε)n); each implies the printed claim
--   - generalization: a (1 + ε)-online thinning strategy, whose target density is chosen from the points retained so far → any density rule determined measurably by the inputs of the earlier steps, with values in [1 − ε/2, 1 + ε/2] on the cube (first clause), and in addition with integral one (second clause, IsThinningDensity); reason: every strategy of §2.1 satisfies the first clause's hypotheses; the second clause covers the reading of 'target density' as a probability density (p.9 says Haar-thinning's µ_t 'is a probability density satisfying the requirement', and Fact 2.3 needs it), so the item holds under either reading
--   - encoding: the number of samples used → n plus the number of rejecting steps among the first n; reason: each step reads x_t and, when it rejects x_t, one more sample y_t
--   - generalization: the algorithm's own randomness (i.i.d. uniform samples and coins) → any probability space carrying measurable, mutually independent inputs with the uniform laws (IsStreamInput); reason: the canonical product space is one such space (proved in the sanity file); every statement about the law of the run specializes to it
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Proposition 2.4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_QMCBeyondHK_IsThinningDensity

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Proposition 2.4, printed p.7 (PDF p.9) of arXiv:2609.10921 (sha256 bc273e88…): with high
probability, any `(1 + ε)`-online thinning strategy uses at most `(1 + O(ε))n` samples.

**Formalization Note** Pinned explicitly: there is an absolute `c > 0` such that the
probability that the `n` steps consume (`n` samples `x_t` plus one `y_t` per rejection) more
than `(1 + 2ε)n` samples is at most `exp(−cεn)` for every strategy whose target densities are
determined measurably by the earlier steps and take values in `[1 − ε/2, 1 + ε/2]` on the cube (the
printed proof), and more than `(1 + ε)n` samples with probability at most `exp(−cεn)` when, in
addition, `∫ μ_t = 1` (`IsThinningDensity`, the probability-density reading of "target density"). -/
theorem proposition_2_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 1 ≤ d → ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (ε : ℝ), 0 < ε → ε < 1 → ∀ (n : ℕ), 1 ≤ n →
      ∀ (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ),
      IsStreamInput P X Ξ Y →
      (∀ (μ : ℕ → Ω → (Fin d → ℝ) → ℝ),
        (∀ t, @Measurable (Ω × (Fin d → ℝ)) ℝ
          (@Prod.instMeasurableSpace Ω (Fin d → ℝ) (stepSigma X Ξ Y t) _) _ (fun p => μ t p.1 p.2)) →
        (∀ t ω x, x ∈ cube d → 1 - ε / 2 ≤ μ t ω x ∧ μ t ω x ≤ 1 + ε / 2) →
        P {ω | (1 + 2 * ε) * (n : ℝ) < ((n + frameRejections ε μ X Ξ n ω : ℕ) : ℝ)}
          ≤ ENNReal.ofReal (Real.exp (-(c * ε * n)))) ∧
      (∀ (μ : ℕ → Ω → (Fin d → ℝ) → ℝ), IsThinningDensity ε X Ξ Y μ →
        P {ω | (1 + ε) * (n : ℝ) < ((n + frameRejections ε μ X Ξ n ω : ℕ) : ℝ)}
          ≤ ENNReal.ofReal (Real.exp (-(c * ε * n)))) := by sorry

end QMCBeyondHK
