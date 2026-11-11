-- Prove2me | Theorems.Thm_SYKLearn_lemma_4_2
-- name    : SYKLearn.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:56.446428+00:00
-- url     : https://prove2.me/theorems/3bea5f00-8d7a-441d-a209-e8125a059e8f
-- title:
--   Lemma 4.2 — continuity and monotonicity of scores: $\partial_a\mathrm{Score}_a(\delta)\ge0$, $|\mathrm{Score}_b(\delta)-\mathrm{Score}_a(\delta)|\le\frac{2}{e\beta}|b-a|$
-- statement:
--   Fix $\beta>0$ and an outcome $\delta\in\mathbb R$, and let $\mathrm{Score}_a(\delta)$ be the score of Definition 4. Then
--
--   1. $\dfrac{d}{da}\mathrm{Score}_a(\delta)\ge0$ for every $a$, and $a\mapsto\mathrm{Score}_a(\delta)$ is non-decreasing;
--   2. for all $a,b\ge\tfrac12$,
--   $$|\mathrm{Score}_b(\delta)-\mathrm{Score}_a(\delta)|\le\frac{2}{e\beta}|b-a|;$$
--   3. $a\mapsto\mathrm{Score}_a(\delta)$ is continuous.
--
--   Averaging over $\delta$, the same properties hold for the average score, which is what makes binary search over the scale sound.
--
--   **Formalization Note** The derivative is Mathlib's `deriv`; monotonicity is stated as well. The Lipschitz bound fails for $a$ near $0$ (at $\beta=1$, $\delta=10$ the derivative at $a=0$ is $10>2/e$), so it is stated for $a,b\ge1/2$.
--
--   Differences from the source:
--   - generalization: scores over the fixed interval a ∈ [1/2, 2] (sentence before the lemma, and its proof) → derivative, monotonicity and continuity for every real a; the Lipschitz bound for all a, b ≥ 1/2; reason: the derivative formula holds for every a and the bound ∂_a Score ≤ 1/(eβa) ≤ 2/(eβ) holds for a ≥ 1/2; restricting to [1/2, 2] gives the page's statement
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 4.2, p.35

import Mathlib
import Definitions.Def_SYKLearn_Experiment

noncomputable section

namespace SYKLearn

/-- **Lemma 4.2 (Continuity and monotonicity of scores)**, p.35 (Anshu–Arunachalam–Chen–Hwang,
*Efficiently Learning SYK Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). At any
`δ`, `(d/da) Score_a(δ) ≥ 0`. Moreover, `|Score_b(δ) − Score_a(δ)| ≤ (2/(eβ))|b − a|`, and thus
`Score_a(δ)` is continuous in `a`.

**Formalization Note.** The page states this for scores over the fixed interval `[1/2, 2]`
(sentence before the lemma; proof). The derivative bound and monotonicity are stated for every real
`a`, and the Lipschitz bound for all `a, b ≥ 1/2`; both specialize to `[1/2, 2]`. The Lipschitz
bound fails for `a` near `0` (at `β = 1`, `δ = 10` the derivative at `a = 0` is `10 > 2/e`).
Continuity is stated for every real `a`. `β > 0` is the known inverse temperature. -/
theorem lemma_4_2 (β : ℝ) (hβ : 0 < β) (δ : ℝ) :
    (∀ a : ℝ, 0 ≤ deriv (fun a => score β a δ) a) ∧
    Monotone (fun a => score β a δ) ∧
    (∀ a b : ℝ, 1 / 2 ≤ a → 1 / 2 ≤ b →
      |score β b δ - score β a δ| ≤ 2 / (Real.exp 1 * β) * |b - a|) ∧
    Continuous (fun a => score β a δ) := by sorry

end SYKLearn
