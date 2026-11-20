-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_hub_inflation_costs
-- name    : StableMSR.Recovery.Supplement.hub_inflation_costs
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-19T15:25:14.99818+00:00
-- url     : https://prove2.me/theorems/f07f28cd-b519-4db2-b73d-41e710d4e0b1
-- title:
--   Cost of the supplied partition and canonical competitor after hub inflation
-- statement:
--   In the hub-and-dummy construction for Proposition C.2, let $R_0$ be the original hub-to-source distance and let $D$ be the source diameter. Write $a$ for the minimum cost of an exact-$k$ partition of the source and $\delta$ for the dummy-to-dummy distance. Assume $1\le k\le n$ and $\delta\ge 0$. For any $s\ge R_0\ge D$, replace all hub-to-source distances by $s$ in both directions.
--
--   The supplied partition then has cost $s$. The source-plus-hub cluster has eccentricity $s$ at every center, and each dummy singleton has radius zero. A distinct exact-$(k+2)$ partition has cost $\delta+a$. It consists of an optimal exact-$k$ source partition, the hub singleton, and all $k+1$ dummy points together. Each of those clusters uses only unchanged distances.
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Proposition C.2, p. 25; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Supplement_Hub

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

theorem hub_inflation_costs {n k : ℕ} (d : Point n → Point n → ℝ) (γ τ s : ℝ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray d)
    (hD : diameter d Finset.univ ≤ hubRadius d γ τ)
    (hs : hubRadius d γ τ ≤ s) (hδ : 0 ≤ dummyDistance d γ τ) :
    let dp := hubDistance d k γ τ
    let p := fun (x y : Point (n + k + 2)) =>
      if (x.val = n ∧ y.val < n) ∨ (y.val = n ∧ x.val < n) then s else dp x y
    cost p (suppliedPartition n k) = s ∧
      ∃ Q, Feasible Finset.univ (k + 2) Q ∧ Q ≠ suppliedPartition n k ∧
        cost p Q = dummyDistance d γ τ + optimumValue d k := by sorry

end StableMSR.Recovery.Supplement
