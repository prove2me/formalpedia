-- Prove2me | Theorems.Thm_VarianceRegularization_Localized_robust_minimizer_oracle
-- name    : VarianceRegularization.Localized.robust_minimizer_oracle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:43:26.571099+00:00
-- url     : https://prove2.me/theorems/efff5f77-f8ee-47b9-831b-08ce32a03208
-- title:
--   Theorem 4, (23) — oracle inequality for every robust minimizer (corrected: probability 1 − 4e^{−t}, constant 182/45)
-- statement:
--   Let $P$ be a probability measure on $\mathcal X$ and $x_1,\dots,x_n$ an i.i.d. sample from $P$, $n\ge1$, with empirical distribution $\widehat P_n$. For $M\ge1$, let $\mathcal F$ be a collection of measurable functions $f:\mathcal X\to[0,M]$, let $\psi_n$ be a sub-root function satisfying the localization inequality (20), and let $r_n^\star>0$ with $r_n^\star\ge\psi_n(r_n^\star)$. Let $0<t<n$ and assume that $\rho$ satisfies
--   $$
--   \frac\rho n\ \ge\ 8\Big(\frac{45M}{n}\Big(t+\log\Big\lceil\log\frac nt\Big\rceil\Big)+18r_n^\star\Big).\qquad(21)
--   $$
--   Then, with probability at least $1-4e^{-t}$, every $\widehat f\in\mathcal F$ that minimizes the robust risk $\sup_{P:\,D_\phi(P\|\widehat P_n)\le\rho/n}\mathbb E_P[f]$ over $\mathcal F$ satisfies
--   $$
--   \mathbb E[\widehat f]\ \le\ \Big(1+2\sqrt{\frac{2\rho}n}\Big)\inf_{f\in\mathcal F}\Big(\mathbb E[f]+\sqrt{\frac{182\rho}{45n}\mathrm{Var}(f)}\Big)+\Big(14+6\sqrt{\frac{2\rho}n}\Big)\frac{M(3\rho+t)}n .
--   $$
--
--   The robustly regularized minimizer thus competes with the best trade-off between risk and standard deviation in the class, with the class complexity entering only through the localized fixed point $r_n^\star$; for classes with small $r_n^\star$ this gives rates faster than $1/\sqrt n$ when the variance at the optimum is small.
--
--   **Formalization Note** Two corrections to the printed statement, both from the proof on p. 41. (i) The paper prints probability $1-3e^{-t}$; the proof combines (22), which holds with probability $1-2e^{-t}$, with Bernstein's inequality and Lemma A.1 for a fixed $f$ (probability $1-2e^{-t}$ together), which gives $1-4e^{-t}$. (ii) The paper prints $\sqrt{\frac{91\rho}{45n}\mathrm{Var}(f)}$; the proof bounds $\sqrt{\frac{2t}n\mathrm{Var}(f)}+\sqrt{\frac{2\rho}n\mathrm{Var}(f)}=\sqrt{\frac{2\mathrm{Var}(f)}n}(\sqrt\rho+\sqrt t)$ using $\sqrt\rho+\sqrt t\le\sqrt{91\rho/45}$, which yields $\sqrt{\frac{182\rho}{45n}\mathrm{Var}(f)}$. The statement covers every minimizer and is not vacuous when no minimizer exists (the failure event then is empty). The conditions $r_n^\star>0$ and $t<n$ are as in (22). The infimum is over $\mathcal F$, whose values are bounded below by $0$.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), pp. 14–15, Theorem 4, (21) and (23); proof p. 41 (probability and constant corrected)

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Localized

/-- **Theorem 4, inequality (23)** (pp. 14–15), in the form its proof establishes. For `M ≥ 1`, let
`F` be a collection of measurable functions `f : X → [0, M]`, `ψ_n` a sub-root function satisfying
the localization inequality (20), and `r⋆_n > 0` with `r⋆_n ≥ ψ_n(r⋆_n)`. Let `0 < t < n` and assume (21):
`ρ/n ≥ 8((45M/n)(t + log ⌈log (n/t)⌉) + 18 r⋆_n)`. Then with probability at least `1 − 4e^{−t}`, every
minimizer `f̂ ∈ F` of the robust risk `sup_{P : D_φ(P‖P̂_n) ≤ ρ/n} E_P[f]` over `F` satisfies
`E[f̂] ≤ (1 + 2√(2ρ/n)) inf_{f ∈ F} (E[f] + √((182ρ/(45n)) Var(f))) + (14 + 6√(2ρ/n)) M(3ρ + t)/n`.

Corrections. (i) The paper prints probability `1 − 3e^{−t}`; its proof (p. 41) combines (22), which
holds with probability `1 − 2e^{−t}`, with Bernstein's inequality and Lemma A.1 for a fixed `f`
(probability `1 − 2e^{−t}`), hence `1 − 4e^{−t}`. (ii) The paper prints `91ρ/(45n)`; its proof bounds
`√(2t Var(f)/n) + √(2ρ Var(f)/n) = √(2 Var(f)/n)(√ρ + √t)` using `√ρ + √t ≤ √(91ρ/45)`, which gives
`√((182ρ/(45n)) Var(f))`; the factor `2` was dropped. `r⋆_n > 0` and `t < n` are domain conditions
of the page. The infimum is over the subtype `F`, whose values are bounded below by `0`. -/
theorem robust_minimizer_oracle {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (M t ρ rstar : ℝ)
    (ψ : ℝ → ℝ) (hM : 1 ≤ M) (ht : 0 < t) (htn : t < n)
    (hmeas : ∀ f ∈ F, Measurable f) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc 0 M)
    (hψ : IsSubRoot ψ) (hloc : LocalizationBound P n F ψ)
    (hrstar : 0 < rstar) (hfix : ψ rstar ≤ rstar)
    (hρ : 8 * (45 * M / n * (t + Real.log (⌈Real.log (n / t)⌉ : ℝ)) + 18 * rstar) ≤ ρ / n) :
    (Measure.pi (fun _ : Fin n => P))
        {s | ∃ g ∈ F, (∀ f ∈ F, robustRisk ρ s g ≤ robustRisk ρ s f) ∧
          (1 + 2 * Real.sqrt (2 * ρ / n))
              * (⨅ f : F, ((∫ x, (f : X → ℝ) x ∂P)
                  + Real.sqrt (182 * ρ / (45 * n) * variance (f : X → ℝ) P)))
            + (14 + 6 * Real.sqrt (2 * ρ / n)) * (M * (3 * ρ + t) / n)
          < ∫ x, g x ∂P}
        ≤ ENNReal.ofReal (4 * Real.exp (-t)) := by sorry

end VarianceRegularization.Localized
