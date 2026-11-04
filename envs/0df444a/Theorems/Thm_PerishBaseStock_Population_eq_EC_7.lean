-- Prove2me | Theorems.Thm_PerishBaseStock_Population_eq_EC_7
-- name    : PerishBaseStock.Population.eq_EC_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:41.968759+00:00
-- url     : https://prove2.me/theorems/6430c5de-4662-42ab-a60e-d277641a3dde
-- title:
--   (EC.7) — $\mathbb E[D(n)]=\mu\mathbb E[N(n)]$ and $\mathrm{Var}[D(n)]=\sigma^2\mathbb E[N(n)]+\mu^2\mathrm{Var}[N(n)]$
-- statement:
--   Let $\hat D_1,\hat D_2,\dots$ be i.i.d. non-negative with mean $\mu>0$ and variance $\sigma^2<\infty$, and let $X_1,X_2,\dots$ be i.i.d. non-negative with mean one, finite variance and a finite exponential moment, independent of the $\hat D_j$. For a positive integer $n$ let $N(n)=\sup\{N:\sum_{k=1}^N X_k/n\le1\}$ and $D(n)=\sum_{j=1}^{N(n)}\hat D_j$. Then $N(n)$ and $D(n)$ have finite second moments, and
--   $$
--   \mathbb E[D(n)]=\mu\,\mathbb E[N(n)],\qquad \mathrm{Var}[D(n)]=\sigma^2\,\mathbb E[N(n)]+\mu^2\,\mathrm{Var}[N(n)] .
--   $$
--
--   These are Wald's equation and the law of total variance for a random sum whose count is independent of the summands.
--
--   **Formalization Note** The finiteness of the second moments is stated as part of the conclusion, so the identities are between genuine moments.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec4, App. B.1, (EC.7)

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-- **(EC.7)** (Bu, Gong & Chao, App. B.1, p. ec4). For every positive integer `n`, `N(n)` and
`D(n) = Σ_{j=1}^{N(n)} D̂_j` have finite second moments, and
`E[D(n)] = μ E[N(n)]`, `Var[D(n)] = σ² E[N(n)] + μ² Var[N(n)]`. -/
theorem eq_EC_7 (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh) (n : ℕ) (hn : 1 ≤ n) :
    MemLp (fun ω : PopSample => ((arrivalCount n ω.2).toNat : ℝ)) 2 (popSampleLaw Dh X) ∧
    MemLp (fun ω : PopSample => (compoundDemand n ω : ℝ)) 2 (popSampleLaw Dh X) ∧
    ∫ ω, (compoundDemand n ω : ℝ) ∂popSampleLaw Dh X =
      customerMean Dh * ∫ ω, ((arrivalCount n ω.2).toNat : ℝ) ∂popSampleLaw Dh X ∧
    variance (fun ω : PopSample => (compoundDemand n ω : ℝ)) (popSampleLaw Dh X) =
      customerVariance Dh * ∫ ω, ((arrivalCount n ω.2).toNat : ℝ) ∂popSampleLaw Dh X +
        customerMean Dh ^ 2 * variance (fun ω : PopSample => ((arrivalCount n ω.2).toNat : ℝ))
          (popSampleLaw Dh X) := by sorry

end PerishBaseStock.Population
