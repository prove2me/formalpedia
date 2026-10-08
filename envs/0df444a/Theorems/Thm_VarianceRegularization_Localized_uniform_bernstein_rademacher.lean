-- Prove2me | Theorems.Thm_VarianceRegularization_Localized_uniform_bernstein_rademacher
-- name    : VarianceRegularization.Localized.uniform_bernstein_rademacher
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:42:44.542078+00:00
-- url     : https://prove2.me/theorems/135e4637-3292-47de-9f4c-ba7e10cf7f0a
-- title:
--   Lemma D.1 — uniform Bernstein inequality with Rademacher complexity, both directions
-- statement:
--   Let $P$ be a probability measure on $\mathcal X$ and $x_1,\dots,x_n$ an i.i.d. sample from $P$, $n\ge1$. Let $M>0$, $r>0$, $t>0$ with $nr>M^2t$, and let $\mathcal F$ be a collection of measurable functions $f:\mathcal X\to[0,M]$ with $\mathrm{Var}(f(X))\le r$ for every $f\in\mathcal F$. Write
--   $$
--   L=t+\log\Big\lceil\log\frac{nr}{M^2t}\Big\rceil .
--   $$
--   Then, with probability at least $1-e^{-t}$, for every $f\in\mathcal F$,
--   $$
--   \mathbb E[f]\ \le\ \mathbb E_{\widehat P_n}[f]+\sqrt{\frac{2e\,\mathrm{Var}(f)}{n}\,L}+6\,\mathbb E[\mathfrak R_n(\mathcal F)]+\frac{7M}{n}\,L .
--   $$
--   The same statement holds, with probability at least $1-e^{-t}$, with the roles of $\mathbb E[f]$ and $\mathbb E_{\widehat P_n}[f]$ reversed.
--
--   The lemma is a Bernstein-type bound uniform over the class: the deviation of each function scales with its own standard deviation, at the price of a doubly logarithmic term from peeling.
--
--   **Formalization Note** The conditions $M>0$ and $nr>M^2t$ make $\log\frac{nr}{M^2t}>0$, so its ceiling is at least $1$ and the outer logarithm is defined, as the page presupposes. The expected Rademacher complexity is assumed integrable over the sample; each direction is its own probability bound; probabilities of non-measurable events are outer measures.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 39, Lemma D.1

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Localized

/-- **Lemma D.1** (p. 39). Let `r > 0` and `F` a collection of measurable functions
`f : X → [0, M]` with `Var(f(X)) ≤ r`. Write `L = t + log ⌈log (n r / (M² t))⌉`. Then with
probability at least `1 − e^{−t}`, for every `f ∈ F`,
`E[f] ≤ E_{P̂_n}[f] + √((2e Var(f)/n) L) + 6 E[ℜ_n(F)] + (7M/n) L`,
and the same holds with the roles of `E[f]` and `E_{P̂_n}[f]` reversed (a separate probability
bound). Domain conditions: `M > 0` and `n r > M² t` make `log(n r/(M² t)) > 0`, so its ceiling is
at least `1` and the outer logarithm is defined, as the page presupposes; `t > 0`. The expected
Rademacher complexity is assumed integrable. -/
theorem uniform_bernstein_rademacher {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (M r t : ℝ)
    (hM : 0 < M) (hr : 0 < r) (ht : 0 < t) (hnr : M ^ 2 * t < n * r)
    (hmeas : ∀ f ∈ F, Measurable f) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc 0 M)
    (hvar : ∀ f ∈ F, variance f P ≤ r)
    (hint : Integrable (fun s : Fin n → X => empRademacher F s)
      (Measure.pi fun _ : Fin n => P)) :
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, empMean s f
            + Real.sqrt (2 * Real.exp 1 * variance f P / n
                * (t + Real.log (⌈Real.log (n * r / (M ^ 2 * t))⌉ : ℝ)))
            + 6 * expRademacher P n F
            + 7 * M / n * (t + Real.log (⌈Real.log (n * r / (M ^ 2 * t))⌉ : ℝ))
          < ∫ x, f x ∂P}
        ≤ ENNReal.ofReal (Real.exp (-t)) ∧
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, (∫ x, f x ∂P)
            + Real.sqrt (2 * Real.exp 1 * variance f P / n
                * (t + Real.log (⌈Real.log (n * r / (M ^ 2 * t))⌉ : ℝ)))
            + 6 * expRademacher P n F
            + 7 * M / n * (t + Real.log (⌈Real.log (n * r / (M ^ 2 * t))⌉ : ℝ))
          < empMean s f}
        ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end VarianceRegularization.Localized
