-- Prove2me | Theorems.Thm_TimeScaleAvg_lemma_4
-- name    : TimeScaleAvg.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:08:58.314273+00:00
-- url     : https://prove2.me/theorems/b222ac9c-a768-4510-8038-1a7cfd92eeb6
-- title:
--   Lemma 4 — weighted averages of a vanishing function vanish
-- statement:
--   Let $\delta\ge0$ and let $a:[\delta,+\infty[\to\mathbb R_+$ satisfy $\lim_{s\to+\infty}a(s)=0$. Then, for every $p>0$,
--
--   $$
--   \lim_{s\to+\infty}A(s)=0,\qquad\text{where}\quad A(s)=\frac{1}{s^p}\int_{\delta}^{s}u^{p-1}a(u)\,du.
--   $$
--
--   This is the averaging step of the proof: vanishing quantities remain vanishing under the weights of $\mu_s$.
--
--   **Formalization Note** The integrability of $u\mapsto u^{p-1}a(u)$ on each $[\delta,s]$ is an explicit hypothesis, so that $A(s)$ is defined.
--
--   Differences from the source:
--   - reading: the printed integral starts at s₀, which the statement does not introduce → lower limit δ; reason: s₀ is the left end of the domain of a
--   - reading: a a "positive" function with values in ℝ₊ → 0 ≤ a s on Set.Ici δ; reason: the values lie in ℝ₊, and the nonnegative reading is the more general one
--   - encoding: A(s) written with no integrability condition → hypothesis: u ↦ u^(p−1) a(u) is integrable on each [δ,s]; reason: this only excludes the cases where A(s) has no meaning: a non-measurable a, or a divergent integral at δ = 0
--   - encoding: a defined on [δ,+∞] → a : ℝ to ℝ, constrained on Set.Ici δ only; reason: values below δ enter no hypothesis and no conclusion
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Lemma 4, p.28

import Mathlib

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Lemma 4 (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.28). Let `δ ≥ 0` and `a : [δ, +∞[ → ℝ₊`
with `lim_{s→+∞} a(s) = 0`. Then, for `p > 0`, `lim_{s→+∞} A(s) = 0`, where
`A(s) = (1/s^p) ∫_{δ}^{s} u^{p-1} a(u) du`.

**Formalization Note.** The lower limit printed `s₀` is the left end `δ` of the domain. The
hypothesis `hint` says that `A(s)` is defined: `u ↦ u^{p-1} a(u)` is integrable on each `[δ, s]`.
Here `δ` is a left endpoint, not a small tolerance: `δ = 0` is allowed. -/
theorem lemma_4 {δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 < p) {a : ℝ → ℝ}
    (ha_nonneg : ∀ s ∈ Set.Ici δ, 0 ≤ a s) (ha : Tendsto a atTop (𝓝 0))
    (hint : ∀ s ∈ Set.Ici δ, IntegrableOn (fun u => u ^ (p - 1) * a u) (Set.Icc δ s)) :
    Tendsto (fun s => (1 / s ^ p) * ∫ u in δ..s, u ^ (p - 1) * a u) atTop (𝓝 0) := by sorry

end TimeScaleAvg
