-- Prove2me | Theorems.Thm_ReviewProvision_proposition_3
-- name    : ReviewProvision.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:12.502854+00:00
-- url     : https://prove2.me/theorems/f03dbcf7-ad85-4b2a-87a4-6a7fd721b554
-- title:
--   Proposition 3, p.23 — FP dominates AP and GP, with a unique symmetric optimum
-- statement:
--   Let $N\ge2$. There is $k_0>0$ such that $(k_0,\dots,k_0)$ is optimal for FP and every optimum of FP equals it. In particular the optimal first-period prices of FP are equal across clusters:
--
--   $$
--   p^*_{n1}=p^*_{l1}\qquad\text{for all }n,l.
--   $$
--
--   Moreover AP and GP each have an optimum, and its profit is strictly below $\Pi_F(k_0,\dots,k_0)$.
--
--   Full information is the most profitable of the three policies, and it needs no price discrimination between ex-ante identical clusters.
--
--   Differences from the source:
--   - reading: 'generates a higher revenue' → strict inequality; reason: the stronger reading; the printed proof writes ≥, and strictness follows from uniqueness of the FP optimum, Lemma 11 and Lemma 2
--   - reading: optimal profit Π*_ψ → a maximizer over feasible ~k, with existence in the conclusion; reason: the optima of AP and GP exist because Π_ψ is continuous on k ≥ 0 and tends to −∞
--   - generalization: Assumption 1 restricts AP and GP (p.16) → no Assumption 1; reason: under Assumption 1 the optimum over all ~k is the paper's Π*_ψ by Proposition 1, so the statement specializes to the source
--   - encoding: prices p_{n1} → sales k_n, with p_{n1} = (1 − k_n)/h; reason: the transformation of p.15
--   - reading: the feasible sales are not stated → k_n ≥ 0 for all n, with no upper bound; reason: the proofs use k_N ≥ 0 and evaluate at k_N = 0 (pp.37, 44); (27) has no multiplier, and an upper bound k_n ≤ 1 is not intended since the optimum can exceed 1
--   - generalization: the optimal first-period prices for FP are symmetric and unique → also the common optimal sales k₀ are positive; reason: p.45 shows k*_{FN} > 0; dropping the clause gives the printed statement
--   - encoding: prior mean q_p, ratings r_n, clusters {1, …, N} → q_p = 1, the statistic y_n = w_n(q + t_n) + √w_n ε_n, Fin N; reason: as in §3.1 and §3.3; y_n = w_n r_n when w_n > 0 and is 0 when no ratings exist
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), Proposition 3, p.23

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Proposition 3**, SSRN 3403322 (manuscript of 2021-05-24), p.23 (PDF 23): FP generates a higher
revenue than both AP and GP, and the optimal first-period prices of FP are symmetric and unique. For
`N ≥ 2`, FP has a unique optimum, it is a symmetric positive vector `(k₀, …, k₀)`, its first-period
prices are equal across clusters, and AP and GP each have an optimum with strictly lower profit.

**Formalization Note.** "Higher" is read strictly. Optima are maximizers, so existence is part of
the conclusion. Assumption 1 is not assumed. -/
theorem proposition_3 (p : Params) {N : ℕ} (hN : 2 ≤ N) :
    ∃ k₀ : ℝ, 0 < k₀ ∧
      IsOptimal p .FP (fun _ : Fin N => k₀) ∧
      (∀ k : Fin N → ℝ, IsOptimal p .FP k → k = fun _ => k₀) ∧
      (∀ k : Fin N → ℝ, IsOptimal p .FP k →
        ∀ n l, firstPeriodPrice p k n = firstPeriodPrice p k l) ∧
      (∃ kA : Fin N → ℝ, IsOptimal p .AP kA ∧
        profit p .AP kA < profit p .FP (fun _ : Fin N => k₀)) ∧
      (∃ kG : Fin N → ℝ, IsOptimal p .GP kG ∧
        profit p .GP kG < profit p .FP (fun _ : Fin N => k₀)) := by sorry

end ReviewProvision
