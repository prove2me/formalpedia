-- Prove2me | Theorems.Thm_PoSShares_Stability_eq_A31
-- name    : PoSShares.Stability.eq_A31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:55.325157+00:00
-- url     : https://prove2.me/theorems/1ad51140-eac8-480b-bdff-c9eb16c82b81
-- title:
--   (A31) — $\mathbb{P}(|X-\pi_1|>\varepsilon) \ge \frac{\pi_1(1-\pi_1)-\varepsilon^2}{1-\varepsilon^2} > 0$
-- statement:
--   Let $\pi_1 \in (0, 1)$ and let $X$ be a random variable with values in $[0, 1]$ almost surely, with mean $\mathbb{E}X = \pi_1$ and variance $\mathrm{Var}(X) = \pi_1(1 - \pi_1)$. Then for every $\varepsilon \in \big(0, \sqrt{\pi_1(1-\pi_1)}\big)$,
--   $$\mathbb{P}\big(|X - \pi_1| > \varepsilon\big) \ge \frac{\pi_1(1-\pi_1) - \varepsilon^2}{1 - \varepsilon^2} > 0.$$
--
--   In the paper $X = \pi_{1,\infty}$ for $\gamma \ge 1$; the bound does not depend on the initial supply $N$, which rules out concentration as $N \to \infty$.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 24, proof of Proposition 4, (A30)–(A31)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **(A31)**, proof of Proposition 4, p. 24. Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

Let `π_1 ∈ (0, 1)` and let `X` (the paper's `π_{1,∞}`) be a random variable with values in
`[0, 1]` almost surely, mean `π_1` and variance `π_1(1 − π_1)`. For every
`ε ∈ (0, √(π_1(1 − π_1)))`,
`P(|X − π_1| > ε) ≥ (π_1(1 − π_1) − ε^2)/(1 − ε^2) > 0`.

**Formalization Note.** The page derives this for `X = π_{1,∞}` from (A30) using exactly
`|π_{1,∞} − π_1| < 1` a.s., `E π_{1,∞} = π_1` and `Var(π_{1,∞}) = π_1(1 − π_1)`; those are the
hypotheses here. The printed strict inequality `> ε` is kept. -/
theorem eq_A31 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π₁ ε : ℝ) (X : Ω → ℝ) (hπ₁ : π₁ ∈ Set.Ioo (0 : ℝ) 1) (hX : Measurable X)
    (hX01 : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∫ ω, X ω ∂μ = π₁)
    (hvar : variance X μ = π₁ * (1 - π₁))
    (hε : ε ∈ Set.Ioo (0 : ℝ) (Real.sqrt (π₁ * (1 - π₁)))) :
    (π₁ * (1 - π₁) - ε ^ 2) / (1 - ε ^ 2) ≤ μ.real {ω | ε < |X ω - π₁|} ∧
      0 < (π₁ * (1 - π₁) - ε ^ 2) / (1 - ε ^ 2) := by sorry

end PoSShares.Stability
