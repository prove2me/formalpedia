-- Prove2me | Theorems.Thm_PerishBaseStock_Population_eq_23
-- name    : PerishBaseStock.Population.eq_23
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:48.952154+00:00
-- url     : https://prove2.me/theorems/1f6c9b36-8b1b-48a8-9c09-a62a551062d1
-- title:
--   (23) — $C(\widetilde S)-\mathrm{OPT}\le\frac{(m-1)\theta}{\lambda me}\big(e^{\lambda S^{NP}_n/m}\,\mathbb E[e^{-\lambda\sum_{j=1}^{N(n)}\hat D_j}]\big)^m$
-- statement:
--   Consider the FIFO perishable inventory system with lifetime $m\ge1$, costs $h>0$, $p>0$, $\theta\ge0$, and generic one-period demand $D(n)=\sum_{j=1}^{N(n)}\hat D_j$ of the population form (7), with $\mathbb E[\hat D_1]>0$. Let $C_n$, $\mathrm{OPT}_n$ and $S^{NP}_n$ be the base-stock cost, the optimal cost and the newsvendor level of this system. For every positive integer $n$, every $\lambda>0$, and every minimizer $\widetilde S$ of $\widetilde C_n$ over $[0,\infty)$,
--   $$
--   C_n(\widetilde S)-\mathrm{OPT}_n\le\frac{(m-1)\theta}{\lambda m e}\Big(e^{\frac1m\lambda S^{NP}_n}\,\mathbb E\Big[e^{-\lambda\sum_{j=1}^{N(n)}\hat D_j}\Big]\Big)^m ,
--   $$
--   where $e$ is Euler's number.
--
--   This is the bound of Theorem 1 evaluated at the population demand; the proof of Theorem 2 bounds its right side.
--
--   **Formalization Note** The gap is stated as $C_n(\widetilde S)\le\mathrm{OPT}_n+\text{RHS}$ in $[0,\infty]$; this is equivalent since $\mathrm{OPT}_n\le C_n(0)<\infty$. The expectation is taken on the joint space of $(\hat D_j)$ and $(X_k)$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 23, (23)

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-- **(23)** (Bu, Gong & Chao, p. 23). With demand of form (7), for every positive integer `n`,
every `λ > 0` and every minimizer `S̃` of `C̃_n`,
`C_n(S̃) - OPT_n ≤ ((m-1)θ/(λme)) (e^{λ S^NP_n / m} E[e^{-λ Σ_{j=1}^{N(n)} D̂_j}])^m`,
stated as `C_n(S̃) ≤ OPT_n + RHS` in `ℝ≥0∞`. -/
theorem eq_23 (c : PerishBaseStock.Lifetime.Params) (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh)
    (P : ℕ → CappedBaseStock.DemandLaw) (hP : IsPopulationFamily Dh X P)
    (n : ℕ) (hn : 1 ≤ n) (lam : ℝ) (hlam : 0 < lam)
    (S : ℝ≥0) (hS : PerishBaseStock.Lifetime.IsHeuristicLevel (P n) c S) :
    baseStockCost (P n) c S ≤
      OPT (P n) c + ENNReal.ofReal
        (((c.m : ℝ) - 1) * c.θ / (lam * (c.m : ℝ) * Real.exp 1) *
          (Real.exp ((1 / (c.m : ℝ)) * lam * (newsvendorLevel (P n) c : ℝ)) *
            ∫ ω, Real.exp (-(lam * (compoundDemand n ω : ℝ))) ∂popSampleLaw Dh X) ^ c.m) := by sorry

end PerishBaseStock.Population
