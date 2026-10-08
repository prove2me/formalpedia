-- Prove2me | Theorems.Thm_VarianceRegularization_Localized_localized_bernstein
-- name    : VarianceRegularization.Localized.localized_bernstein
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:42:55.464216+00:00
-- url     : https://prove2.me/theorems/853b29b8-3742-481e-9e88-61740a94e74b
-- title:
--   Lemma D.2 — localized uniform Bernstein bound in terms of the root r⋆ₙ, both directions
-- statement:
--   Let $P$ be a probability measure on $\mathcal X$ and $x_1,\dots,x_n$ an i.i.d. sample from $P$, $n\ge1$. Let $\mathcal F$ be a collection of measurable functions $f:\mathcal X\to[0,M]$ satisfying the localization inequality (20) for a sub-root function $\psi_n$, and let $r_n^\star>0$ with $\psi_n(r_n^\star)\le r_n^\star$. Let $0<t<n$ and
--   $$
--   B_n=\frac1n\Big(t+\log\Big\lceil\log\frac nt\Big\rceil\Big).
--   $$
--   Then, with probability at least $1-e^{-t}$, for every $f\in\mathcal F$,
--   $$
--   \mathbb E[f]\ \le\ \mathbb E_{\widehat P_n}[f]+\Big(\sqrt{2eB_n}+6\sqrt{r_n^\star+7MB_n/3}\Big)\sqrt{\mathbb E[f^2]}+6r_n^\star+14MB_n .
--   $$
--   The same statement holds, with probability at least $1-e^{-t}$, with the roles of $\mathbb E[f]$ and $\mathbb E_{\widehat P_n}[f]$ reversed.
--
--   The global Rademacher complexity of Lemma D.1 is replaced by the local quantity $r_n^\star$, and the deviation scales with the second moment $\mathbb E[f^2]$ of each function.
--
--   **Formalization Note** The page assumes $\psi_n$ has "root" $r_n^\star$; the statement uses $r_n^\star>0$ and $\psi_n(r_n^\star)\le r_n^\star$, which is the property the proof uses and the one Theorem 4 supplies. The condition $0<t<n$ makes $\lceil\log(n/t)\rceil\ge1$, so $B_n$ is defined. Each direction is its own probability bound.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 39, Lemma D.2 (proof pp. 42–43)

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Localized

/-- **Lemma D.2** (p. 39). Let `F` be a collection of measurable functions `f : X → [0, M]`
satisfying the localization inequality (20) for a sub-root function `ψ_n` with root `r⋆_n`. Let
`B_n = (1/n)(t + log ⌈log (n/t)⌉)`. Then with probability at least `1 − e^{−t}`, for every `f ∈ F`,
`E[f] ≤ E_{P̂_n}[f] + (√(2e B_n) + 6 √(r⋆_n + 7 M B_n / 3)) √(E[f²]) + 6 r⋆_n + 14 M B_n`,
and the same holds with the roles of `E[f]` and `E_{P̂_n}[f]` reversed (a separate probability
bound). "Root" is taken as `r⋆ > 0` with `ψ_n(r⋆) ≤ r⋆` (the only property the proof on pp. 42–43
uses, and the one Theorem 4 supplies). `0 < t < n` makes `⌈log(n/t)⌉ ≥ 1`, so `B_n` is defined. -/
theorem localized_bernstein {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (M t rstar : ℝ)
    (ψ : ℝ → ℝ) (ht : 0 < t) (htn : t < n)
    (hmeas : ∀ f ∈ F, Measurable f) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc 0 M)
    (hψ : IsSubRoot ψ) (hloc : LocalizationBound P n F ψ)
    (hrstar : 0 < rstar) (hfix : ψ rstar ≤ rstar) :
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, empMean s f
            + (Real.sqrt (2 * Real.exp 1 * ((1 / (n : ℝ)) * (t + Real.log (⌈Real.log (n / t)⌉ : ℝ))))
              + 6 * Real.sqrt (rstar
                  + 7 * M * ((1 / (n : ℝ)) * (t + Real.log (⌈Real.log (n / t)⌉ : ℝ))) / 3))
              * Real.sqrt (∫ x, f x ^ 2 ∂P)
            + 6 * rstar + 14 * M * ((1 / (n : ℝ)) * (t + Real.log (⌈Real.log (n / t)⌉ : ℝ)))
          < ∫ x, f x ∂P}
        ≤ ENNReal.ofReal (Real.exp (-t)) ∧
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, (∫ x, f x ∂P)
            + (Real.sqrt (2 * Real.exp 1 * ((1 / (n : ℝ)) * (t + Real.log (⌈Real.log (n / t)⌉ : ℝ))))
              + 6 * Real.sqrt (rstar
                  + 7 * M * ((1 / (n : ℝ)) * (t + Real.log (⌈Real.log (n / t)⌉ : ℝ))) / 3))
              * Real.sqrt (∫ x, f x ^ 2 ∂P)
            + 6 * rstar + 14 * M * ((1 / (n : ℝ)) * (t + Real.log (⌈Real.log (n / t)⌉ : ℝ)))
          < empMean s f}
        ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end VarianceRegularization.Localized
