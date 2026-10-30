-- Prove2me | Theorems.Thm_RefDemandLearning_SlowMoving_proposition_1
-- name    : RefDemandLearning.SlowMoving.proposition_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T05:22:47.401731+00:00
-- url     : https://prove2.me/theorems/5e84c496-66e8-4ac5-aeb8-d660bf2b87dc
-- title:
--   Proposition 1 — convergence rate of the reference price
-- statement:
--   Let $I=[\ell,u]$ with $0\le\ell<u$ and let $\rho$ be a continuous interval-valued reference mechanism. Suppose that, for some $\zeta\in[0,1)$ and every feasible history, $r_{t+1}=\zeta r_t+(1-\zeta)p_t$.
--
--   There exists a finite constant $c_2>0$ such that for all positive integers $s<t$, all price histories $p_1,\ldots,p_s\in I$ and every held price $p\in I$,
--   $$\sum_{k=s+1}^{t}|\rho_k(p_1,\ldots,p_s,\underbrace{p,\ldots,p}_{k-s-1})-p|\le c_2.$$
--   The constant is uniform in both endpoints, the history and the held price. This bounds the sum of absolute deviations, not merely each deviation or a limiting value. The case $\zeta=0$ is included. No demand-model or noise assumptions are needed for this mechanism-only assertion.
--
--   **Formalization Note.** The proof's available choice $(u-\ell)/(1-\zeta)$ explains the constant's scale; the source's stated conclusion is existential and is kept that way.
--
--   Differences from the source:
--   - encoding: periods start at 1 and positive integer horizons → period n represents source period n+1; horizons and interval endpoints retain explicit positive-natural guards; reason: finite histories use Fin n and finite sums are reindexed without changing any term
-- source:
--   den Boer and Keskin, Dynamic Pricing with Demand Learning and Reference Effects, DOI https://doi.org/10.1287/mnsc.2021.4234, supplied April 19, 2021 artifact, Proposition 1, printed p. 13, PDF p. 13

import Definitions.Def_RefDemandLearning_SlowMoving_Mechanism

set_option autoImplicit false

namespace RefDemandLearning.SlowMoving

theorem proposition_1 (I : PriceInterval) (ρ : Mechanism I) (hρ : IsES ρ) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ s t : ℕ, 1 ≤ s → s < t →
      ∀ (h : Fin s → Price I) (p : Price I), trackingError ρ s t h p ≤ c₂ := by sorry

end RefDemandLearning.SlowMoving
