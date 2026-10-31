-- Prove2me | Theorems.Thm_TimeScaleAvg_lemma_2
-- name    : TimeScaleAvg.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:08:55.900195+00:00
-- url     : https://prove2.me/theorems/d786d2ec-d7e1-4a20-ac6b-7ef62769f4e2
-- title:
--   Lemma 2 — Gronwall–Bellman
-- statement:
--   Let $T\ge\delta\ge0$, let $g:[\delta,T]\to\mathbb R_+$ be integrable, and let $c\ge0$. Suppose that $h:[\delta,T]\to\mathbb R$ is continuous and
--
--   $$
--   \frac12h^2(t)\le\frac12c^2+\int_\delta^t h(u)g(u)\,du\qquad\text{for every }t\in[\delta,T].
--   $$
--
--   Then
--
--   $$
--   |h(t)|\le c+\int_\delta^t g(u)\,du\qquad\text{for every }t\in[\delta,T].
--   $$
--
--   This is the tool that handles the perturbation $g$ in the analysis of (6).
--
--   Differences from the source:
--   - reading: the display writes ∫_δ^t h(t) g(t) dt → ∫ u in δ..t, h u * g u; reason: the integration variable of the display is a dummy
--   - encoding: g, h defined on [δ,T] → g, h : ℝ to ℝ, constrained on Set.Icc δ T only; reason: values outside [δ,T] enter no hypothesis and no conclusion
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Lemma 2, p.28

import Mathlib

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Lemma 2, Gronwall–Bellman (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.28). Let `T ≥ δ ≥ 0`,
`g : [δ, T] → ℝ₊` integrable, `c ≥ 0`, and `h : [δ, T] → ℝ` continuous with
`(1/2) h²(t) ≤ (1/2) c² + ∫_δ^t h(u) g(u) du` for every `t ∈ [δ, T]`. Then
`|h(t)| ≤ c + ∫_δ^t g(u) du` for every `t ∈ [δ, T]`.

**Formalization Note.** The display of the paper reuses `t` as the integration variable, which is a
dummy. Here `δ` is a left endpoint, not a small tolerance: `δ = 0` is allowed. -/
theorem lemma_2 {δ T c : ℝ} (hδ : 0 ≤ δ) (hT : δ ≤ T) {g h : ℝ → ℝ}
    (hg_nonneg : ∀ t ∈ Set.Icc δ T, 0 ≤ g t) (hg : IntegrableOn g (Set.Icc δ T)) (hc : 0 ≤ c)
    (hh : ContinuousOn h (Set.Icc δ T))
    (hineq : ∀ t ∈ Set.Icc δ T,
      (1 / 2) * h t ^ 2 ≤ (1 / 2) * c ^ 2 + ∫ u in δ..t, h u * g u) :
    ∀ t ∈ Set.Icc δ T, |h t| ≤ c + ∫ u in δ..t, g u := by sorry

end TimeScaleAvg
