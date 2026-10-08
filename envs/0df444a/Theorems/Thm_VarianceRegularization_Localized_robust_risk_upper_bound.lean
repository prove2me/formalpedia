-- Prove2me | Theorems.Thm_VarianceRegularization_Localized_robust_risk_upper_bound
-- name    : VarianceRegularization.Localized.robust_risk_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:43:11.46783+00:00
-- url     : https://prove2.me/theorems/cfe8134a-362d-4294-95ee-1061ee6d2a5f
-- title:
--   Theorem 4, (22) — the robust risk upper-bounds the population risk uniformly (probability 1 − 2e^{−t})
-- statement:
--   Let $P$ be a probability measure on $\mathcal X$ and $x_1,\dots,x_n$ an i.i.d. sample from $P$, $n\ge1$. For $M\ge1$, let $\mathcal F$ be a collection of measurable functions $f:\mathcal X\to[0,M]$, let $\psi_n$ be a sub-root function satisfying the localization inequality (20), and let $r_n^\star>0$ with $r_n^\star\ge\psi_n(r_n^\star)$. Let $0<t<n$ and assume that $\rho$ satisfies
--   $$
--   \frac\rho n\ \ge\ 8\Big(\frac{45M}{n}\Big(t+\log\Big\lceil\log\frac nt\Big\rceil\Big)+18r_n^\star\Big).\qquad(21)
--   $$
--   Then, with probability at least $1-2e^{-t}$,
--   $$
--   \mathbb E[f]\ \le\ \Big(1+2\sqrt{\frac{2\rho}n}\Big)\sup_{P:\,D_\phi(P\|\widehat P_n)\le\rho/n}\mathbb E_P[f]+\Big(13+4\sqrt{\frac{2\rho}n}\Big)\frac{M\rho}n\qquad\text{for all }f\in\mathcal F.
--   $$
--
--   The robust risk is thus a uniform high-probability upper bound on the population risk, with a complexity term entering only through $r_n^\star$ in the choice of $\rho$.
--
--   **Formalization Note** The paper prints probability $1-e^{-t}$; its proof on pp. 40–41 intersects the events of Lemmas D.2 and D.3 and concludes "with probability at least $1-2e^{-t}$. This is the first result (22)." The condition $r_n^\star>0$ reflects that the page calls $r_n^\star$ a root and the proof divides by $\sqrt{r_n^\star}$; $t<n$ makes $\log\lceil\log(n/t)\rceil$ defined. The failure event is "some $f\in\mathcal F$ violates the bound", measured by the product measure (an outer measure if not measurable).
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), pp. 14–15, Theorem 4, (21)–(22); proof pp. 40–41 (probability corrected)

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Localized

/-- **Theorem 4, inequality (22)** (pp. 14–15), with the probability its proof establishes. For
`M ≥ 1`, let `F` be a collection of measurable functions `f : X → [0, M]`, `ψ_n` a sub-root function
satisfying the localization inequality (20), and `r⋆_n > 0` with `r⋆_n ≥ ψ_n(r⋆_n)`. Let `0 < t < n` and
assume (21): `ρ/n ≥ 8((45M/n)(t + log ⌈log (n/t)⌉) + 18 r⋆_n)`. Then with probability at least
`1 − 2e^{−t}`, for all `f ∈ F`,
`E[f] ≤ (1 + 2√(2ρ/n)) sup_{P : D_φ(P‖P̂_n) ≤ ρ/n} E_P[f] + (13 + 4√(2ρ/n)) M ρ / n`.

Correction: the paper prints probability `1 − e^{−t}`; its proof (pp. 40–41) intersects the events
of Lemmas D.2 and D.3 and concludes "with probability at least `1 − 2e^{−t}`. This is the first
result (22)." `r⋆_n > 0` (the page calls `r⋆_n` a root, and the proof divides by `√r⋆_n`) and
`t < n` (so that `log ⌈log (n/t)⌉` is defined) are domain conditions of the page. -/
theorem robust_risk_upper_bound {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (M t ρ rstar : ℝ)
    (ψ : ℝ → ℝ) (hM : 1 ≤ M) (ht : 0 < t) (htn : t < n)
    (hmeas : ∀ f ∈ F, Measurable f) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc 0 M)
    (hψ : IsSubRoot ψ) (hloc : LocalizationBound P n F ψ)
    (hrstar : 0 < rstar) (hfix : ψ rstar ≤ rstar)
    (hρ : 8 * (45 * M / n * (t + Real.log (⌈Real.log (n / t)⌉ : ℝ)) + 18 * rstar) ≤ ρ / n) :
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ f ∈ F, (1 + 2 * Real.sqrt (2 * ρ / n)) * robustRisk ρ s f
            + (13 + 4 * Real.sqrt (2 * ρ / n)) * (M * ρ / n) < ∫ x, f x ∂P}
        ≤ ENNReal.ofReal (2 * Real.exp (-t)) := by sorry

end VarianceRegularization.Localized
