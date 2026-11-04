-- Prove2me | Theorems.Thm_PerishBaseStock_Population_eq_EC_8
-- name    : PerishBaseStock.Population.eq_EC_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:46.80253+00:00
-- url     : https://prove2.me/theorems/2298a594-f324-4129-bde7-75d320a5c979
-- title:
--   (EC.8) — $\mathbb E[e^{-\lambda D(n)}]\le e^{-\delta^2n/(8(1+\delta)^2\nu^2)}+(\mathbb E[e^{-\lambda\hat D_1}])^{n/(1+\delta)}$
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. non-negative random variables with $\mathbb E[X_1]=1$, finite variance and $\mathbb E[e^{sX_1}]<\infty$ for some $s>0$. There is a constant $\nu>0$, depending only on the distribution of $X_1$, with the following property. Let $\hat D_1,\hat D_2,\dots$ be any i.i.d. non-negative random variables with finite variance and positive mean, independent of the $X_k$, let $N(n)=\sup\{N:\sum_{k=1}^N X_k/n\le1\}$, and let $\lambda>0$. For every $0<\delta<\nu$ and every integer $n\ge2(1+\delta)/\delta$,
--   $$
--   \mathbb E\Big[\exp\Big(-\lambda\sum_{j=1}^{N(n)}\hat D_j\Big)\Big]\le\exp\Big(-\frac{\delta^2n}{8(1+\delta)^2\nu^2}\Big)+\big(\mathbb E[e^{-\lambda\hat D_1}]\big)^{\frac{n}{1+\delta}} .
--   $$
--
--   Together with the step-1 claim this makes the right side of (23) exponentially small in $n$.
--
--   **Formalization Note** The order of quantifiers ($\nu$ is chosen from the law of $X_1$ before the law of $\hat D_1$, $\delta$, $n$ and $\lambda$) encodes "depends only on the distribution of $X_1$". The power $n/(1+\delta)$ is a real power of a number in $(0,1]$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec4, App. B.1, (EC.8)

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-- **(EC.8)** (Bu, Gong & Chao, App. B.1, p. ec4). There is a constant `ν > 0`, depending only on
the distribution of `X_1`, such that for every customer-demand law, every `0 < δ < ν`, every
`n ≥ 2(1+δ)/δ` and every `λ > 0`,
`E[exp(-λ Σ_{j=1}^{N(n)} D̂_j)] ≤ exp(-δ²n/(8(1+δ)²ν²)) + (E[e^{-λ D̂_1}])^{n/(1+δ)}`. -/
theorem eq_EC_8 (X : InterarrivalLaw) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (Dh : CustomerLaw), 0 < customerMean Dh →
      ∀ δ : ℝ, 0 < δ → δ < ν →
      ∀ n : ℕ, 2 * (1 + δ) / δ ≤ (n : ℝ) → ∀ lam : ℝ, 0 < lam →
        ∫ ω, Real.exp (-(lam * (compoundDemand n ω : ℝ))) ∂popSampleLaw Dh X ≤
          Real.exp (-(δ ^ 2 * (n : ℝ) / (8 * (1 + δ) ^ 2 * ν ^ 2))) +
            (∫ x : ℝ≥0, Real.exp (-(lam * (x : ℝ))) ∂Dh.law) ^ ((n : ℝ) / (1 + δ)) := by sorry

end PerishBaseStock.Population
