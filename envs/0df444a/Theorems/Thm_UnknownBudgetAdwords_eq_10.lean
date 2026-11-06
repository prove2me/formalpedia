-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_eq_10
-- name    : UnknownBudgetAdwords.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:32.736975+00:00
-- url     : https://prove2.me/theorems/ed9186b0-d3ee-4206-ab59-50b10e834e9a
-- title:
--   Inequality (10): GPG against f-GPG on augmented budgets, per resource (corrected: Algorithm 2 step)
-- statement:
--   Let $\beta>0$, let $Y\in[0,1]^n$ be a seed vector without ties and let $i$ be a resource. Then
--
--   $$
--   \frac{B_i^a}{B_i}\,\mathrm{GPG}_i(Y)\ge\text{f-GPG}_i^a(Y),
--   $$
--
--   where $\mathrm{GPG}_i(Y)$ is the revenue from $i$ in GPG on the original instance and $\text{f-GPG}_i^a(Y)$ is the revenue from $i$ in f-GPG on the augmented instance.
--
--   Summing over $i$ and taking expectations gives (11), which relates the budget-oblivious algorithm to the fractional one.
--
--   Differences from the source:
--   - correction: Algorithm 2 steps by δ_{i*}(t) = min{1, B_{i*}(t−1)/b_{i*,t}}, with the argmax over I(t) → each pass matches d = min(1 − δ, R_{i*}/b_{i*,t}), with the argmax over available resources with a positive bid; reason: on budgets (0.5, 10) and one arrival with bids (1, 1) the printed step matches 1.5 of one arrival, against "until t is fully (fractionally) matched" (p.10) and the continuous description of p.16; a zero bid would also be divided by
--   - reading: "arbitrary seed Y", with ties excluded in the proof as having probability 0 (p.24) → the hypothesis TieFree I β Y; reason: the proof needs w = e, which uses that bid prices differ; ties_null shows the hypothesis holds almost surely
--   - encoding: seeds Y ∈ [0,1]ⁿ → unitSeeds Y; reason: the same condition
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, (10), p.22

import Definitions.Def_UnknownBudgetAdwords_Augment
import Definitions.Def_UnknownBudgetAdwords_Generic
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds unitSeeds)
noncomputable section

namespace UnknownBudgetAdwords

/-- Inequality (10) (Udwani, arXiv:2110.00504v5, (10), p.22): for a seed `Y` and a resource `i`,
`(B_i^a / B_i) GPG_i(Y) ≥ f-GPG_i^a(Y)`.

**Formalization Note** "Arbitrary seed" excludes the seeds with ties, as the proof does on p.24
("w.p. 1"); that exclusion is `TieFree`. -/
theorem eq_10 {N M : ℕ} (I : Instance N M) (β : ℝ) (hβ : 0 < β) (Y : Seeds N) (hY : unitSeeds Y) (hT : TieFree I β Y) (i : Fin N) : fUsed (augment I) β Y i ≤ (augment I).budget i / I.budget i * spend I (gpgAlloc I β Y) i M := by sorry

end UnknownBudgetAdwords
