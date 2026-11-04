-- Prove2me | Theorems.Thm_PerishBaseStock_Population_renewal_limits
-- name    : PerishBaseStock.Population.renewal_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:42.234976+00:00
-- url     : https://prove2.me/theorems/8c96ccba-5556-46af-8f47-33b3bd4d77be
-- title:
--   Renewal limits — $\mathbb E[N(n)]/n\to1$ and $\mathrm{Var}[N(n)]/n\to\sigma_X^2$
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. non-negative random variables with $\mathbb E[X_1]=1$, variance $\sigma_X^2<\infty$ and $\mathbb E[e^{sX_1}]<\infty$ for some $s>0$, and let $N(n)=\sup\{N\in\mathbb N:\sum_{k=1}^N X_k/n\le1\}$ be the number of renewals in $[0,n]$. Then
--   $$
--   \lim_{n\to\infty}\frac{\mathbb E[N(n)]}{n}=1,\qquad \lim_{n\to\infty}\frac{\mathrm{Var}[N(n)]}{n}=\sigma_X^2 .
--   $$
--
--   The first limit is the elementary renewal theorem; the second is the asymptotic variance of a renewal counting process with finite-variance inter-arrival times.
--
--   **Formalization Note** $n$ runs over the natural numbers. Expectation and variance are taken under the i.i.d. product law of $(X_k)$, with $N(n)$ read as a natural number (it is finite almost surely).
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec4, App. B.1, display after (EC.7)

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-- **Renewal limits** (Bu, Gong & Chao, App. B.1, p. ec4). Since `E[X_1] = 1` and
`Var[X_1] = σ_X²`, `E[N(n)]/n → 1` and `Var[N(n)]/n → σ_X²` as `n → ∞`. -/
theorem renewal_limits (X : InterarrivalLaw) :
    Tendsto (fun n : ℕ =>
        (∫ x, ((arrivalCount n x).toNat : ℝ) ∂interarrivalSeqLaw X) / (n : ℝ))
      atTop (nhds 1) ∧
    Tendsto (fun n : ℕ =>
        variance (fun x => ((arrivalCount n x).toNat : ℝ)) (interarrivalSeqLaw X) / (n : ℝ))
      atTop (nhds (interarrivalVariance X)) := by sorry

end PerishBaseStock.Population
