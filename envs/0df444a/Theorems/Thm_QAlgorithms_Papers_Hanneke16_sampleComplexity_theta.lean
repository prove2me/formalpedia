-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Hanneke16_sampleComplexity_theta
-- name    : QAlgorithms.Papers.Hanneke16.sampleComplexity_theta
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:03:03.117152+00:00
-- url     : https://prove2.me/theorems/17a8f649-92e7-428f-8500-bdcae6f08523
-- title:
--   Hanneke: optimal PAC sample complexity Θ((d + Log(1/δ))/ε)
-- statement:
--   This is the optimal sample complexity of realizable PAC learning (Hanneke, Theorem 2 and Corollary 3).
--
--   Let $\mathcal X$ be a nonempty measurable space (the instance space) and let $\mathcal C$ be a set of measurable classifiers $h:\mathcal X\to\{-1,+1\}$ with $|\mathcal C|\ge 3$ and finite VC dimension $d$. For a probability measure $P$ on $\mathcal X$, a target $f^\star\in\mathcal C$ and a classifier $h$, write $\mathrm{er}_P(h;f^\star)=P(x: h(x)\ne f^\star(x))$. For $\varepsilon,\delta\in(0,1)$ the sample complexity $M(\varepsilon,\delta)\in\mathbb N\cup\{\infty\}$ is the smallest $m$ for which some (possibly randomized) learning algorithm $A$, given the $m$ i.i.d. $P$-distributed points labelled by $f^\star$, outputs a measurable classifier $\hat h$ with $\mathbb P(\mathrm{er}_P(\hat h;f^\star)\le\varepsilon)\ge 1-\delta$ for every $P$ and every $f^\star\in\mathcal C$ (and $\infty$ if no $m$ works). Let $\mathrm{Log}(z)=\ln(\max\{z,e\})$. Assume, as the paper does, that the events of the uniform convergence bound for sample-consistent classifiers are measurable.
--
--   Then there are numerical constants, independent of $\mathcal X$ and $\mathcal C$ (in particular of $d$):
--
--   1. $\varepsilon_0,\delta_0\in(0,1)$ and $c_0>0$ such that for all $\varepsilon\in(0,\varepsilon_0)$, $\delta\in(0,\delta_0)$, $M(\varepsilon,\delta)$ is finite and
--   $$M(\varepsilon,\delta)\le \frac{c_0}{\varepsilon}\Big(d+\mathrm{Log}\frac1\delta\Big);$$
--   2. $\varepsilon_1,\delta_1\in(0,1)$ and $c_1>0$ such that for all $\varepsilon\in(0,\varepsilon_1)$, $\delta\in(0,\delta_1)$,
--   $$\frac{1}{\varepsilon}\Big(d+\mathrm{Log}\frac1\delta\Big)\le c_1\, M(\varepsilon,\delta).$$
--
--   This removes the logarithmic factor $\mathrm{Log}(1/\varepsilon)$ from the classical upper bound of Vapnik and Blumer et al., matching the lower bounds of Blumer et al. and Ehrenfeucht et al. up to constants.
--
--   **Formalization Note** $M(\varepsilon,\delta)$ takes values in $\mathbb N\cup\{\infty\}$ (`ℕ∞`); part 2 is stated for finite values only, the infinite case being trivially true. Randomized algorithms use an arbitrary probability space independent of the sample. The PAC failure probability is the measure of the failure set (its outer measure if that set is not measurable).
-- source:
--   The Optimal Sample Complexity of PAC Learning (Hanneke), arXiv:1507.00473v4, Theorem 2 and Corollary 3, PDF p. 7. https://arxiv.org/abs/1507.00473v4 . PDF SHA-256: d38eee0540492b280c82f0454f04d69b96a33f2f94f46559cf25fa1b541c6a43.

import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
set_option autoImplicit false

namespace QAlgorithms.Papers.Hanneke16

open QAlgorithms.Learning

universe u

/-- Hanneke p.7, Theorem 2 and Corollary 3: `M(ε, δ) = Θ((1/ε)(d + Log(1/δ)))`.

The `O`/`Ω` notation is the paper's (p.3): there are numerical constants `ε₀, δ₀ ∈ (0, 1)` and
`c₀ ∈ (0, ∞)`, "independent of `C` and `X`" (so `c₀` cannot depend on `d`), such that the bound
holds for all `ε ∈ (0, ε₀)`, `δ ∈ (0, δ₀)`. The constants are therefore quantified before the
instance space and the concept class.

1. (Theorem 2, the `O` half) `M(ε, δ)` is finite and `M(ε, δ) ≤ c₀ (d + Log(1/δ)) / ε`.
2. (the `Ω` half, bound (1) p.3) `(d + Log(1/δ)) / ε ≤ c₁ M(ε, δ)`, read as trivially true
   when `M(ε, δ) = ∞`.

Standing assumptions (pp.1–3): `X` nonempty with a σ-algebra; every `h ∈ C` measurable;
`|C| ≥ 3`; `d < ∞` (p.3, "for the remainder of this article we suppose d < ∞"); and p.3: "we
adopt the assumption that the events appearing in probability claims below are indeed
measurable. For our purposes, this comes into effect only in the application of classic
generalization bounds for sample-consistent classifiers (Lemma 4 below)." That assumption is
`ConsistentEventsMeasurable C`: the events of Lemma 4 (some `h ∈ C` consistent with the sample
has error above a threshold) are measurable for every `P`, `f⋆ ∈ C`, `m`. -/
theorem sampleComplexity_theta :
    (∃ ε0 δ0 c0 : ℝ, 0 < ε0 ∧ ε0 < 1 ∧ 0 < δ0 ∧ δ0 < 1 ∧ 0 < c0 ∧
      ∀ (X : Type u) [MeasurableSpace X] [Nonempty X] (C : Set (X → Bool)) (d : ℕ),
        (∀ c ∈ C, Measurable c) → 3 ≤ C.encard → vcDimSet C = (d : ℕ∞) →
        ConsistentEventsMeasurable C →
        ∀ ε δ : ℝ, 0 < ε → ε < ε0 → 0 < δ → δ < δ0 →
          ∃ m : ℕ, pacSampleComplexity C ε δ = (m : ℕ∞) ∧
            (m : ℝ) ≤ c0 * (((d : ℝ) + logE (1 / δ)) / ε)) ∧
    (∃ ε1 δ1 c1 : ℝ, 0 < ε1 ∧ ε1 < 1 ∧ 0 < δ1 ∧ δ1 < 1 ∧ 0 < c1 ∧
      ∀ (X : Type u) [MeasurableSpace X] [Nonempty X] (C : Set (X → Bool)) (d : ℕ),
        (∀ c ∈ C, Measurable c) → 3 ≤ C.encard → vcDimSet C = (d : ℕ∞) →
        ConsistentEventsMeasurable C →
        ∀ ε δ : ℝ, 0 < ε → ε < ε1 → 0 < δ → δ < δ1 →
          ∀ m : ℕ, pacSampleComplexity C ε δ = (m : ℕ∞) →
            ((d : ℝ) + logE (1 / δ)) / ε ≤ c1 * (m : ℝ)) := by
  sorry

end QAlgorithms.Papers.Hanneke16
