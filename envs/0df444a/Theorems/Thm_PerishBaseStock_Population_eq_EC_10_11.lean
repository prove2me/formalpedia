-- Prove2me | Theorems.Thm_PerishBaseStock_Population_eq_EC_10_11
-- name    : PerishBaseStock.Population.eq_EC_10_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:47.590987+00:00
-- url     : https://prove2.me/theorems/c8f20dde-7cc3-412a-8f5b-3594b768a9c4
-- title:
--   (EC.10)–(EC.11) — $\mathbb P(N(n)<n/(1+\delta))\le\exp(-\delta^2n/(8(1+\delta)^2\nu^2))$
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. non-negative random variables with $\mathbb E[X_1]=1$, finite variance and $\mathbb E[e^{sX_1}]<\infty$ for some $s>0$, and let $N(n)=\sup\{N\in\mathbb N:\sum_{k=1}^N X_k/n\le1\}$. There is a constant $\nu>0$, depending only on the distribution of $X_1$, such that for every $0<\delta<\nu$ and every integer $n\ge 2(1+\delta)/\delta$,
--   $$
--   \mathbb P\Big(N(n)<\frac{n}{1+\delta}\Big)\le\exp\Big(-\frac{\delta^2 n}{8(1+\delta)^2\nu^2}\Big).
--   $$
--
--   This lower-deviation bound for the renewal count is the probabilistic input of (EC.8).
--
--   **Formalization Note** The event $N(n)<n/(1+\delta)$ requires $N(n)$ to be finite. The statement involves only the law of $X_1$, so $\nu$ depends only on it.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. ec4–ec5, App. B.1, (EC.10)–(EC.11)

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-- **(EC.10)–(EC.11) claim** (Bu, Gong & Chao, App. B.1, pp. ec4–ec5). There is a constant
`ν > 0`, depending only on the distribution of `X_1`, such that for every `0 < δ < ν` and every
`n ≥ 2(1+δ)/δ`, `P(N(n) < n/(1+δ)) ≤ exp(-δ²n/(8(1+δ)²ν²))`. -/
theorem eq_EC_10_11 (X : InterarrivalLaw) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ δ : ℝ, 0 < δ → δ < ν →
      ∀ n : ℕ, 2 * (1 + δ) / δ ≤ (n : ℝ) →
        interarrivalSeqLaw X
            {x | ∃ N : ℕ, arrivalCount n x = (N : ℕ∞) ∧ (N : ℝ) < (n : ℝ) / (1 + δ)} ≤
          ENNReal.ofReal (Real.exp (-(δ ^ 2 * (n : ℝ) / (8 * (1 + δ) ^ 2 * ν ^ 2)))) := by sorry

end PerishBaseStock.Population
