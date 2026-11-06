-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_eq_13
-- name    : UnknownBudgetAdwords.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:39.170383+00:00
-- url     : https://prove2.me/theorems/655e8ec5-1697-48e0-b181-07d40ed4733e
-- title:
--   Inequality (13): the coupling of GPG with f-GPG on augmented budgets (corrected: Algorithm 2 step)
-- statement:
--   Let $\beta>0$, and let $Y\in[0,1]^n$ be a seed vector without ties. For every resource $j$ and every $t$ from the first arrival to $T+1$,
--
--   $$
--   z_j^{a,f}(t,Y)\ge z_j(t,Y).
--   $$
--
--   Here $z_j(t,Y)=(B_j-x_j(t,Y))^+$ and $z_j^{a,f}(t,Y)=(B_j-x_j^{a,f}(t,Y))^+$, where $x_j(t,Y)$ and $x_j^{a,f}(t,Y)$ are the budget of $j$ used before arrival $t$ in GPG on the original instance and in f-GPG on the augmented instance.
--
--   So at every point in time, f-GPG on the augmented instance has used, measured against the original budget, no more than GPG has. This is what makes (10) possible even though the two algorithms can produce very different matchings.
--
--   Differences from the source:
--   - correction: Algorithm 2 steps by δ_{i*}(t) = min{1, B_{i*}(t−1)/b_{i*,t}}, with the argmax over I(t) → each pass matches d = min(1 − δ, R_{i*}/b_{i*,t}), with the argmax over available resources with a positive bid; reason: on budgets (0.5, 10) and one arrival with bids (1, 1) the printed step matches 1.5 of one arrival, against "until t is fully (fractionally) matched" (p.10) and the continuous description of p.16; a zero bid would also be divided by
--   - reading: "arbitrary seed Y", with ties excluded in the proof as having probability 0 (p.24) → the hypothesis TieFree I β Y; reason: the proof needs w = e, which uses that bid prices differ; ties_null shows the hypothesis holds almost surely
--   - reading: x_j^{a,f}, x_j called the "remaining budget" (p.22) → the budget used; reason: z would vanish at the first arrival otherwise, and (14) says the set {j | z_j(t, Y) > 0} is the available set of GPG
--   - generalization: (13) for t ∈ T → for t = 1, …, T + 1; reason: p.23 uses the index T + 1; the statement specializes to the printed range
--   - encoding: seeds Y ∈ [0,1]ⁿ → unitSeeds Y; reason: the same condition
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, (13), p.23; definitions of x, p.22, and z, p.23

import Definitions.Def_UnknownBudgetAdwords_Augment
import Definitions.Def_UnknownBudgetAdwords_Generic
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds unitSeeds)
noncomputable section

namespace UnknownBudgetAdwords

/-- Inequality (13) (Udwani, arXiv:2110.00504v5, (13), p.23): for every resource `j` and every
arrival index, `z_j^{a,f}(t, Y) ≥ z_j(t, Y)`.

**Formalization Note** `t` runs over `0, …, M`, the paper's `1, …, T + 1`: p.23 uses the index
`T + 1`. The paper's exclusion of ties is `TieFree`. -/
theorem eq_13 {N M : ℕ} (I : Instance N M) (β : ℝ) (hβ : 0 < β) (Y : Seeds N) (hY : unitSeeds Y) (hT : TieFree I β Y) (j : Fin N) (t : ℕ) (ht : t ≤ M) : zGPG I β Y j t ≤ zAug I β Y j t := by sorry

end UnknownBudgetAdwords
