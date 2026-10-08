-- Prove2me | Theorems.Thm_VarianceRegularization_Localized_localized_second_moment
-- name    : VarianceRegularization.Localized.localized_second_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:43:03.973993+00:00
-- url     : https://prove2.me/theorems/a5b44f69-bdce-4c9f-82de-121f4e58f3ee
-- title:
--   Lemma D.3 (corrected constants) — two-sided localized bounds on second moments
-- statement:
--   Let $P$ be a probability measure on $\mathcal X$ and $x_1,\dots,x_n$ an i.i.d. sample from $P$, $n\ge1$. Let $M\ge1$ and let $\mathcal F$ be a collection of measurable functions $f:\mathcal X\to[0,M]$ satisfying the localization inequality (20) for a sub-root function $\psi_n$, with $r_n^\star>0$ and $\psi_n(r_n^\star)\le r_n^\star$. Let $\eta>0$ and $t>0$. Then, with probability at least $1-e^{-t}$, for every $f\in\mathcal F$,
--   $$
--   \mathbb E[f^2]\ \le\ \Big(1+\frac1\eta\Big)\mathbb E_{\widehat P_n}[f^2]+72M^2(1+\eta)r_n^\star+\Big(4(1+\eta)+\frac{14}3\Big)\frac{M^2t}n ,
--   $$
--   and, with probability at least $1-e^{-t}$, for every $f\in\mathcal F$,
--   $$
--   \mathbb E_{\widehat P_n}[f^2]\ \le\ \Big(1+\frac1{1+\eta}\Big)\mathbb E[f^2]+72M^2(1+\eta)r_n^\star+\Big(4(1+\eta)+\frac{14}3\Big)\frac{M^2t}n .
--   $$
--
--   The lemma transfers second moments between the population and the sample uniformly over the class; with $\eta=1$ it is the step of Theorem 4 that replaces $\mathbb E[f^2]$ by $\mathbb E_{\widehat P_n}[f^2]$.
--
--   **Formalization Note** These are the bounds the proof on pp. 43–44 establishes. The paper prints the additive term $72M^2(1+\eta)r_n^\star+\frac{Mt}{n}(4+\frac73M)$ in both bounds and the coefficient $1+\frac{\eta}{1+\eta}$ in the second; the proof yields $KA^2+2D$ with $K=1+\eta$, $A^2\le 72M^2r_n^\star+4M^2t/n$ and $D=\frac73M^2t/n$, and the coefficient $1+1/K$ in the reversed direction. The hypothesis $M\ge1$ is the standing hypothesis of Theorem 4, whose proof Appendix D is; the proof's step $r\ge K^2A^2\ge r_n^\star$ needs $6(1+\eta)M\ge1$. The page's "root" is used as $r_n^\star>0$, $\psi_n(r_n^\star)\le r_n^\star$.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 40, Lemma D.3 (proof pp. 43–44, constants corrected)

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Localized

/-- **Lemma D.3** (p. 40), in the form its proof (pp. 43–44) establishes. Let `M ≥ 1` and `F` a
collection of measurable functions `f : X → [0, M]` satisfying the localization inequality (20)
for a sub-root `ψ_n` with root `r⋆_n` (`r⋆ > 0`, `ψ_n(r⋆) ≤ r⋆`), and let `η > 0`, `t > 0`. Then
with probability at least `1 − e^{−t}`, for every `f ∈ F`,
`E[f²] ≤ (1 + 1/η) E_{P̂_n}[f²] + 72 M² (1 + η) r⋆_n + (4(1 + η) + 14/3) M² t / n`,
and, with probability at least `1 − e^{−t}`, for every `f ∈ F`,
`E_{P̂_n}[f²] ≤ (1 + 1/(1 + η)) E[f²] + 72 M² (1 + η) r⋆_n + (4(1 + η) + 14/3) M² t / n`.

Corrections. The paper prints the additive term `72 M²(1 + η) r⋆_n + (M t/n)(4 + 7M/3)` and, in the
second bound, the coefficient `1 + η/(1 + η)`. Its proof gives `K A² + 2D` with `K = 1 + η`,
`A² ≤ 72 M² r⋆_n + 4 M² t/n`, `D = 7 M² t/(3n)`, i.e. the term above, and in the reversed
direction the coefficient `1 + 1/K = 1 + 1/(1 + η)`. `M ≥ 1` is Theorem 4's hypothesis, standing
in Appendix D; the proof's step `r ≥ K² A² ≥ r⋆_n` needs `6(1 + η)M ≥ 1`. -/
theorem localized_second_moment {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (M t rstar η : ℝ)
    (ψ : ℝ → ℝ) (hM : 1 ≤ M) (ht : 0 < t) (hη : 0 < η)
    (hmeas : ∀ f ∈ F, Measurable f) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc 0 M)
    (hψ : IsSubRoot ψ) (hloc : LocalizationBound P n F ψ)
    (hrstar : 0 < rstar) (hfix : ψ rstar ≤ rstar) :
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, (1 + 1 / η) * empMean s (fun x => f x ^ 2)
            + 72 * M ^ 2 * (1 + η) * rstar + (4 * (1 + η) + 14 / 3) * M ^ 2 * t / n
          < ∫ x, f x ^ 2 ∂P}
        ≤ ENNReal.ofReal (Real.exp (-t)) ∧
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, (1 + 1 / (1 + η)) * (∫ x, f x ^ 2 ∂P)
            + 72 * M ^ 2 * (1 + η) * rstar + (4 * (1 + η) + 14 / 3) * M ^ 2 * t / n
          < empMean s (fun x => f x ^ 2)}
        ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end VarianceRegularization.Localized
