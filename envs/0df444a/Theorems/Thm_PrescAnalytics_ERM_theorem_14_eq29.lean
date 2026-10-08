-- Prove2me | Theorems.Thm_PrescAnalytics_ERM_theorem_14_eq29
-- name    : PrescAnalytics.ERM.theorem_14_eq29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:41:35.661758+00:00
-- url     : https://prove2.me/theorems/6ec084d7-1a8b-49c1-aaa7-74930a105384
-- title:
--   Theorem 14 (29) — w.p. ≥ 1 − δ, E g(T) ≤ (1/N) Σ g(uⁱ) + ḡ√(log(1/δ)/2N) + ℜ_N(𝒢) for all g ∈ 𝒢 (0 ≤ g ≤ ḡ)
-- statement:
--   Let $P$ be a probability measure on a measurable space $\mathcal U$, and let $\mathcal G$ be a pointwise separable class of measurable functions $g:\mathcal U\to\mathbb R$ with
--   $$0\le g(u)\le\bar g\qquad\text{for all }g\in\mathcal G,\ u\in\mathcal U.$$
--   Let $N\ge1$, $\delta>0$, and let $S_N=(u^1,\dots,u^N)$ be an i.i.d. sample from $P$, i.e. drawn from the product measure $P^N$. Then, with probability at least $1-\delta$,
--   $$\mathbb E[g(T)]\le\frac1N\sum_{i=1}^N g(u^i)+\bar g\sqrt{\frac{\log(1/\delta)}{2N}}+\mathfrak R_N(\mathcal G)\qquad\text{for all }g\in\mathcal G,$$
--   where $T\sim P$ and $\mathfrak R_N(\mathcal G)$ is the marginal Rademacher complexity (factor $2/N$, no absolute value).
--
--   This is the first half of the paper's restatement of the main uniform deviation bound of Bartlett and Mendelson (2003); applied to the cost class of a family of decision rules it gives inequality (26) of Theorem 13.
--
--   **Formalization Note** The paper assumes only $|g|\le\bar g$; the printed statement is false without $g\ge0$ (with $\mathcal G=\{u\mapsto u\}$, $u$ uniform on $\{-1,+1\}$, $N=1$, $\delta=1/5$, the bound fails with probability $1/2$), so the Lean adds $0\le g$ and keeps every printed constant. "With probability $1-\delta$" is stated as: the set of samples on which the inequality fails for some $g\in\mathcal G$ has outer $P^N$-measure at most $\delta$. The inequality is written as $\max(0,\mathbb E g-\hat{\mathbb E}g-\bar g\sqrt{\cdot})\le\mathfrak R_N(\mathcal G)$ in $[0,\infty]$, which is equivalent since $\mathfrak R_N(\mathcal G)\ge0$. Pointwise separability is the added measurability convention. For $\delta\ge1$, Lean's $\sqrt{\log(1/\delta)/(2N)}$ is $0$ and the claim is trivial, as on the page.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 40, Theorem 14, Eq. (29)

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic

namespace PrescAnalytics.ERM

open MeasureTheory

/-- Theorem 14, (29) (p. 40), with the corrected boundedness `0 ≤ g ≤ ḡ`. Let `G` be a pointwise
separable class of measurable functions `U → ℝ` with values in `[0, ḡ]`, `P` a probability measure on
`U`, `N ≥ 1`, `δ > 0`. Outside a set of `P^N`-measure at most `δ`, every sample
`S_N = (u^1, …, u^N)` satisfies
`E[g(T)] ≤ (1/N) Σ_i g(u^i) + ḡ √(log(1/δ)/(2N)) + ℜ_N(G)` for all `g ∈ G` simultaneously
(stated as: the bad set, an outer measure, is `≤ δ`; the inequality is written
`ofReal(E g − Ê g − ḡ√…) ≤ ℜ_N(G)`, equivalent since `ℜ_N(G) ≥ 0`). -/
theorem theorem_14_eq29 {U : Type*} [MeasurableSpace U] (P : Measure U) [IsProbabilityMeasure P]
    (G : Set (U → ℝ)) (gbar : ℝ) (hG_meas : ∀ g ∈ G, Measurable g)
    (hG_sep : IsPointwiseSeparable G) (hG_bdd : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => P)
      {s | ∃ g ∈ G, margRademacherR P N G <
        ENNReal.ofReal ((∫ u, g u ∂P) - empMean s g
          - gbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))} ≤ ENNReal.ofReal δ := by sorry

end PrescAnalytics.ERM
