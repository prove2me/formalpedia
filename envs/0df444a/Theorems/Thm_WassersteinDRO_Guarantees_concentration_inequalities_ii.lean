-- Prove2me | Theorems.Thm_WassersteinDRO_Guarantees_concentration_inequalities_ii
-- name    : WassersteinDRO.Guarantees.concentration_inequalities_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T02:35:08.591781+00:00
-- url     : https://prove2.me/theorems/908f116c-19fb-4c8d-bf93-7fbacf618521
-- title:
--   Theorem 21 — Concentration inequalities II
-- statement:
--   Suppose the unknown true distribution $P$ has mean vector $\mu$ and covariance matrix
--   $\Sigma$, and there are $\alpha>2$, $A>0$ with $E_P[\exp(\|\xi\|_2^\alpha)] \le A$. Then there
--   is $c>1$, depending on $P$ only through $\mu,\Sigma,\alpha,A,m$, such that for any
--   $\eta\in(0,1]$ the sample mean $\hat\mu$ and sample covariance $\hat\Sigma$ satisfy
--   $P^N[(\mu,\Sigma)\in U_\varepsilon(\hat\mu,\hat\Sigma)] \ge 1-\eta$ whenever $\varepsilon \ge
--   \varepsilon_N(\eta) = \log(c/\eta)/\sqrt{N}$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Theorem 21, p. 23, eq. (28)

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_meanVector
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_WassersteinDRO_Guarantees_meanCovarianceUncertaintySet
import Definitions.Def_WassersteinDRO_Guarantees_empiricalDistribution
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- Theorem 21 (Concentration inequalities II), Kuhn et al. 2019, p. 23: suppose the unknown
true distribution `P` has mean vector `µ` and covariance matrix `Σ`, and there are `α > 2`,
`A > 0` with `E_P[exp(‖ξ‖₂^α)] ≤ A`. Then there is `c > 1`, depending on `P` only through
`µ,Σ,α,A,m`, such that for any `η ∈ (0,1]` the sample mean `µ̂` and sample covariance `Σ̂`
satisfy `P^N[(µ,Σ) ∈ U_ε(µ̂,Σ̂)] ≥ 1-η` whenever `ε ≥ ε_N(η) = log(c/η)/√N`. "Depends on `P`
only through `µ,Σ,α,A,m`" is encoded by quantifying `c` before `P` is fixed: a single `c`
works for every `P` sharing the same `(µ,Σ,α,A,m)` (`FAITHFULNESS_TRAPS.md` trap 8). -/
theorem concentration_inequalities_ii {m : ℕ}
    (μ : EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ) (α A : ℝ)
    (hα : 2 < α) (hA : 0 < A) :
    ∃ c : ℝ, c > 1 ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) (N : ℕ),
        IsProbabilityMeasure P → 0 < N →
        meanVector P = μ → covarianceMatrix P = Sigma →
        Integrable (fun x => Real.exp (‖x‖ ^ α)) P →
        (∫ x, Real.exp (‖x‖ ^ α) ∂P) ≤ A →
        ∀ η ε : ℝ, 0 < η → η ≤ 1 → ε ≥ Real.log (c / η) / Real.sqrt N →
          sampleMeasure P N
              {ξhat : Fin N → EuclideanSpace ℝ (Fin m) |
                (μ, Sigma) ∈ meanCovarianceUncertaintySet ε
                  (meanVector (empiricalDistribution ξhat))
                  (covarianceMatrix (empiricalDistribution ξhat))} ≥
            ENNReal.ofReal (1 - η) := by sorry

end WassersteinDRO.Guarantees
