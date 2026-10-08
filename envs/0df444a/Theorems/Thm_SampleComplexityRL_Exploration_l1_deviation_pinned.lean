-- Prove2me | Theorems.Thm_SampleComplexityRL_Exploration_l1_deviation_pinned
-- name    : SampleComplexityRL.Exploration.l1_deviation_pinned
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:10.27972+00:00
-- url     : https://prove2.me/theorems/37fe9646-0aa2-4261-bb79-cd4225d65dd4
-- title:
--   Lemma 8.5.5 (pinned constant) — m ≥ (8N/ε²)log(2N/δ) samples give Σ|p̂(i) − p(i)| ≤ ε with probability > 1 − δ
-- statement:
--   Let $p$ be a probability distribution on a set of $N\ge1$ elements, let $\varepsilon>0$ and $0<\delta<1$, and let $m$ be a number of samples with
--   $$
--   m\ \ge\ \frac{8N}{\varepsilon^2}\,\log\frac{2N}{\delta}.
--   $$
--   Draw $m$ independent samples from $p$ and let $\hat p(i)$ be the fraction of samples equal to $i$. Then, with probability greater than $1-\delta$,
--   $$
--   \sum_{i}\big|\hat p(i)-p(i)\big|\ \le\ \varepsilon.
--   $$
--
--   The point of the lemma is that $O\!\big(\tfrac N{\varepsilon^2}\log\tfrac N\delta\big)$ samples suffice for $\ell_1$ accuracy $\varepsilon$, linear rather than quadratic in $N$; it sets the sample size $m$ of $R_{max}$.
--
--   **Formalization Note** This is a pinned form of the printed $m=O\big(\frac N{\varepsilon^2}\log\frac N\delta\big)$: the constant is the condition $2N\exp(-\varepsilon^2m/(8N))\le\delta$ with which the printed proof ends (p. 113). The samples are independent with law $\mu$ on `Fin N` (product measure on `Fin m → Fin N`), and $p(i)=\mu(\{i\})$.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 112, Lemma 8.5.5 (constant from the last line of its proof, p. 113)

import Mathlib
import Definitions.Def_SampleComplexityRL_Exploration_Empirical

namespace SampleComplexityRL.Exploration

open MeasureTheory

/-- **Lemma 8.5.5, pinned constant** (Kakade 2003, p. 112). Let `p` be a probability distribution
`μ` on a set of `N ≥ 1` elements, let `0 < ε`, `0 < δ < 1`, and let
`m ≥ (8N/ε²) log(2N/δ)` (the condition `2N exp(−ε²m/(8N)) ≤ δ` that ends the printed proof,
p. 113, in place of the printed `m = O((N/ε²) log(N/δ))`). If `m` independent samples are drawn
from `μ` and `p̂` is their empirical distribution, then with probability greater than `1 − δ`,
`Σ_i |p̂(i) − p(i)| ≤ ε`. -/
theorem l1_deviation_pinned (N m : ℕ) (hN : 0 < N) (μ : Measure (Fin N))
    [IsProbabilityMeasure μ] (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : 8 * (N : ℝ) / ε ^ 2 * Real.log (2 * N / δ) ≤ m) :
    ENNReal.ofReal (1 - δ) <
      (Measure.pi fun _ : Fin m => μ)
        {ω | ∑ i, |empiricalDist ω i - (μ {i}).toReal| ≤ ε} := by sorry

end SampleComplexityRL.Exploration
