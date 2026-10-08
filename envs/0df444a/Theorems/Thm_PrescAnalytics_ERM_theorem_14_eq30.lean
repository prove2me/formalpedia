-- Prove2me | Theorems.Thm_PrescAnalytics_ERM_theorem_14_eq30
-- name    : PrescAnalytics.ERM.theorem_14_eq30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:41:35.870462+00:00
-- url     : https://prove2.me/theorems/09625818-421e-4658-91e5-67b5b80b7a27
-- title:
--   Theorem 14 (30) — w.p. ≥ 1 − δ, E g(T) ≤ (1/N) Σ g(uⁱ) + 3ḡ√(log(2/δ)/2N) + ℜ̂_N(𝒢) for all g ∈ 𝒢 (0 ≤ g ≤ ḡ)
-- statement:
--   Let $P$ be a probability measure on a measurable space $\mathcal U$, and let $\mathcal G$ be a pointwise separable class of measurable functions $g:\mathcal U\to\mathbb R$ with $0\le g(u)\le\bar g$ for all $g\in\mathcal G$, $u\in\mathcal U$. Let $N\ge1$, $\delta>0$, and let $S_N=(u^1,\dots,u^N)$ be drawn from $P^N$. Then, with probability at least $1-\delta$,
--   $$\mathbb E[g(T)]\le\frac1N\sum_{i=1}^N g(u^i)+3\bar g\sqrt{\frac{\log(2/\delta)}{2N}}+\widehat{\mathfrak R}_N(\mathcal G;S_N)\qquad\text{for all }g\in\mathcal G,$$
--   where $T\sim P$ and $\widehat{\mathfrak R}_N(\mathcal G;S_N)$ is the empirical Rademacher complexity on the observed sample.
--
--   Unlike (29), this bound involves only quantities computable from the data; applied to the cost class of a family of decision rules it gives inequality (27) of Theorem 13.
--
--   **Formalization Note** As for (29), the paper assumes only $|g|\le\bar g$; the Lean adds $0\le g$ (the bound (29) is false without it, and (30) is not established with the printed constant $3$ under $|g|\le\bar g$) and keeps every printed constant. "With probability $1-\delta$" is the outer-measure bound on the set of samples where the inequality fails for some $g$. The empirical complexity takes values in `EReal`; $+\infty$ makes the inequality hold. Pointwise separability is the added measurability convention.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 40–41, Theorem 14, Eq. (30)

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic

namespace PrescAnalytics.ERM

open MeasureTheory

/-- Theorem 14, (30) (p. 41), with the corrected boundedness `0 ≤ g ≤ ḡ`. Let `G` be a pointwise
separable class of measurable functions `U → ℝ` with values in `[0, ḡ]`, `P` a probability measure on
`U`, `N ≥ 1`, `δ > 0`. Outside a set of `P^N`-measure at most `δ`, every sample
`S_N = (u^1, …, u^N)` satisfies
`E[g(T)] ≤ (1/N) Σ_i g(u^i) + 3ḡ √(log(2/δ)/(2N)) + ℜ̂_N(G; S_N)` for all `g ∈ G` simultaneously,
with the empirical complexity `ℜ̂_N(G; S_N) ∈ EReal`. -/
theorem theorem_14_eq30 {U : Type*} [MeasurableSpace U] (P : Measure U) [IsProbabilityMeasure P]
    (G : Set (U → ℝ)) (gbar : ℝ) (hG_meas : ∀ g ∈ G, Measurable g)
    (hG_sep : IsPointwiseSeparable G) (hG_bdd : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => P)
      {s | ∃ g ∈ G, empRademacherR G s <
        (((∫ u, g u ∂P) - empMean s g
          - 3 * gbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)} ≤ ENNReal.ofReal δ := by sorry

end PrescAnalytics.ERM
