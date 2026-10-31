-- Prove2me | Theorems.Thm_ReviewProvision_eq_3
-- name    : ReviewProvision.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:29.534889+00:00
-- url     : https://prove2.me/theorems/e8c95184-961d-4fe8-97a1-4e3a59f34980
-- title:
--   Eq. (3), p.14 — optimal second-period price and payoff
-- statement:
--   Fix a realized vector $\vec v$ of customer evaluations. In each cluster $n$ the price
--
--   $$
--   p^*_{n2}=\max\{v_n/2h,\,0\}
--   $$
--
--   is the unique maximizer of the revenue $m(v_n-hr)r$ over prices $r\ge0$, the optimal revenue is $m(v_n^+)^2/(4h)$ with $x^+=\max\{x,0\}$, and the optimal second-period payoff is
--
--   $$
--   \Pi_2^*(\vec v)=\sum_{n=1}^N\frac{m(v_n^+)^2}{4h}.
--   $$
--
--   The payoff is the sum of the clusters' revenues with no joint terms, so only the marginal laws of the evaluations matter to the firm.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - generalization: p*_{n2} is the firm's optimal price → p*_{n2} is the unique maximizer over r ≥ 0; reason: uniqueness holds for every real v and implies optimality
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eq. (3), p.14

import Mathlib
import Definitions.Def_ReviewProvision_secondPeriodPayoff

namespace ReviewProvision

/-- **Eq. (3)**, SSRN 3403322 (manuscript of 2021-05-24), p.14 (PDF 14): the optimal second-period
price in a cluster is `p*_{n2} = max{v/2h, 0}`, and the optimal payoff is `Σ_n m (v_n⁺)²/(4h)`.

**Formalization Note.** The first two clauses say that the price `max{v/2h, 0}` is the unique
maximizer of the cluster revenue over prices `r ≥ 0`. -/
theorem eq_3 (p : Params) {N : ℕ} (v : Fin N → ℝ) :
    (∀ n, IsGreatest (clusterRevenue p (v n) '' Set.Ici 0)
      (clusterRevenue p (v n) (max (v n / (2 * p.h)) 0))) ∧
    (∀ n, ∀ r, 0 ≤ r →
      clusterRevenue p (v n) r = clusterRevenue p (v n) (max (v n / (2 * p.h)) 0) →
        r = max (v n / (2 * p.h)) 0) ∧
    (∀ n, optimalRevenue p (v n) = p.m * (max (v n) 0) ^ 2 / (4 * p.h)) ∧
    secondPeriodPayoff p v = ∑ n, p.m * (max (v n) 0) ^ 2 / (4 * p.h) := by sorry

end ReviewProvision
