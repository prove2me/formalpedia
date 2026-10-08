-- Prove2me | Theorems.Thm_VarianceRegularization_Localized_bousquet_talagrand
-- name    : VarianceRegularization.Localized.bousquet_talagrand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:42:33.199223+00:00
-- url     : https://prove2.me/theorems/6459d517-e47a-4b4d-8aa2-8dba471ee209
-- title:
--   Lemma B.2 — Bousquet's form of Talagrand's inequality, both directions
-- statement:
--   Let $P$ be a probability measure on $\mathcal X$, $x_1,\dots,x_n$ an i.i.d. sample from $P$ with $n\ge1$, and $\widehat P_n$ its empirical distribution. Let $r>0$, $t>0$, and let $\mathcal F$ be a class of measurable functions mapping $\mathcal X$ into $[a,b]$ such that $\mathrm{Var}(f(X))\le r$ for every $f\in\mathcal F$. Then, with probability at least $1-e^{-t}$,
--   $$
--   \sup_{f\in\mathcal F}\big\{\mathbb E[f]-\mathbb E_{\widehat P_n}[f]\big\}\ \le\ \inf_{\alpha>0}\Big\{2(1+\alpha)\,\mathbb E[\mathfrak R_n(\mathcal F)]+\sqrt{\frac{2rt}{n}}+\frac tn(b-a)\Big(\frac13+\frac1\alpha\Big)\Big\}.
--   $$
--   The same statement, again with probability at least $1-e^{-t}$, holds with $\sup_{f\in\mathcal F}\big(\mathbb E_{\widehat P_n}[f]-\mathbb E[f]\big)$ on the left.
--
--   This is the concentration inequality behind every uniform bound of Appendix D: it controls the uniform deviation of empirical means by the expected Rademacher complexity and a variance term.
--
--   **Formalization Note** The failure event "the supremum exceeds the infimum" is written as "some $f\in\mathcal F$ and some $\alpha>0$ violate the inequality", which is equivalent and needs no real supremum; its probability under the product measure is an outer measure when the event is not measurable. The two directions are two separate probability bounds. The expected Rademacher complexity is assumed integrable over the sample.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 37, Lemma B.2 (citing Bousquet)

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Localized

/-- **Lemma B.2** (p. 37; Bousquet's version of Talagrand's inequality, cited). Let `r > 0` and
let `F` be a class of measurable functions `X → [a, b]` with `Var(f(X)) ≤ r` for every `f ∈ F`.
Then, with probability at least `1 − e^{−t}`,
`sup_{f ∈ F} {E[f] − E_{P̂_n}[f]} ≤ inf_{α > 0} {2(1 + α) E[ℜ_n(F)] + √(2rt/n) + (t/n)(b − a)(1/3 + 1/α)}`,
and the same holds with `sup_{f ∈ F}(E_{P̂_n}[f] − E[f])` on the left. The two directions are two
separate probability bounds. The bad event "the supremum exceeds the infimum" is written as "some
`f ∈ F` and some `α > 0` violate the inequality"; its measure under `Pⁿ` is an outer measure when
the event is not measurable. The expected Rademacher complexity is assumed integrable. -/
theorem bousquet_talagrand {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (a b r t : ℝ)
    (hr : 0 < r) (ht : 0 < t)
    (hmeas : ∀ f ∈ F, Measurable f) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc a b)
    (hvar : ∀ f ∈ F, variance f P ≤ r)
    (hint : Integrable (fun s : Fin n → X => empRademacher F s)
      (Measure.pi fun _ : Fin n => P)) :
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, ∃ α : ℝ, 0 < α ∧
          2 * (1 + α) * expRademacher P n F + Real.sqrt (2 * r * t / n)
              + t / n * (b - a) * (1 / 3 + 1 / α) < (∫ x, f x ∂P) - empMean s f}
        ≤ ENNReal.ofReal (Real.exp (-t)) ∧
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, ∃ α : ℝ, 0 < α ∧
          2 * (1 + α) * expRademacher P n F + Real.sqrt (2 * r * t / n)
              + t / n * (b - a) * (1 / 3 + 1 / α) < empMean s f - ∫ x, f x ∂P}
        ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end VarianceRegularization.Localized
