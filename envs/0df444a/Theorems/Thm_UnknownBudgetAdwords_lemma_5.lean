-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_lemma_5
-- name    : UnknownBudgetAdwords.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:13.569915+00:00
-- url     : https://prove2.me/theorems/f2c29f99-ecb5-4ef7-96f0-bc437e64a313
-- title:
--   Lemma 5: a lower bound on budget usage (corrected: OPT moments truncated, Algorithm 2 step)
-- statement:
--   Let $\beta>0$, let $i$ be a resource, $Y_{-i}$ seeds in $[0,1]$ for the others without ties among themselves, $\tau$ an allocation and $y_i\in[0,1]$. Suppose that $\text{f-GPG}_i(y_i)<B(y_i)$. Then
--
--   $$
--   \text{f-GPG}_i(y_i)\ge\sum_{v\in V,\ v\ge y_i}b(v)\,\frac{g(v)-g(y_i)}{1-g(y_i)}.
--   $$
--
--   This is the new step of the paper. The dominance property of vertex-weighted matching, $\text{f-GPG}_i(y_i)\ge B(y_i)$, fails for Adwords, and this bound takes its place. The paper shows by Example 4.2 that it is tight.
--
--   Differences from the source:
--   - correction: b(v) and B(y) integrate over all of [t, t+1) for t ∈ OPT_i (p.17) → the moments of OPT_i are truncated to the part of each arrival that fits in the budget, s < cap, so that the sum of b(v) is OPT_i; reason: with budgets (1, 100), one arrival with bids (2, 0.001) matched to the first resource, β = 1, y₂ = 0.5, y₁ = 0, f-GPG₁ = 1 < B(0) = 2 while the right side of Lemma 5 is about 1.9994; the page itself says B(0) = OPT_i and B(y) ≤ B_i
--   - correction: Algorithm 2 steps by δ_{i*}(t) = min{1, B_{i*}(t−1)/b_{i*,t}}, with the argmax over I(t) → each pass matches d = min(1 − δ, R_{i*}/b_{i*,t}), with the argmax over available resources with a positive bid; reason: on budgets (0.5, 10) and one arrival with bids (1, 1) the printed step matches 1.5 of one arrival, against "until t is fully (fractionally) matched" (p.10) and the continuous description of p.16; a zero bid would also be divided by
--   - reading: "given i ∈ I and seed Y_{−i}", with ties excluded in the proofs as having probability 0 (p.19) → the hypothesis GenericOthers I β Y i: no ties among resources other than i, and their seeds below 1; reason: the paper excludes ties in the proof; y_i stays free, since the lemma is for every y_i ∈ [0, 1]; ties_null shows the hypothesis holds almost surely
--   - generalization: OPT_i, the optimal offline allocation → τ any allocation; reason: the proof uses only feasibility of OPT, so the statement specializes to τ optimal
--   - encoding: sums Σ_{v ∈ V} b(v) F(v) over the finite set V of critical thresholds → sumV: Σ_t b_{i,t} ∫_0^{cap_t} F(y^c_{i,t+s}) ds, the same sum over moments; reason: y^c is piecewise constant in s, so this is the same number and no finiteness proof is needed
--   - reading: (g(v) − g(y_i))/(1 − g(y_i)) at y_i = v = 1 is 0/0 → Lean value 0; reason: the lemma stays true there and no hypothesis is added
--   - encoding: seeds Y ∈ [0,1]ⁿ → unitSeeds Y; reason: the same condition
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Lemma 5, p.18; b(v), B(y), p.17

import Definitions.Def_UnknownBudgetAdwords_Thresholds
import Definitions.Def_UnknownBudgetAdwords_Generic
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds unitSeeds)
noncomputable section

namespace UnknownBudgetAdwords

/-- Lemma 5 (Udwani, arXiv:2110.00504v5, Lemma 5, p.18): if `f-GPG_i(y_i) < B(y_i)`, then
`f-GPG_i(y_i) ≥ ∑_{v ∈ V, v ≥ y_i} b(v) (g(v) − g(y_i)) / (1 − g(y_i))`.

**Formalization Note** `b(v)` and `B(y)` are over the moments of `OPT_i` truncated to the budget
(`cap`): the literal formula, over whole arrivals, is false when `OPT_i`'s last bid overshoots.
The proof uses only feasibility of `OPT`, so `τ` is any allocation. At `y_i = v = 1` the printed
`0/0` is Lean's `0`. -/
theorem lemma_5 {N M : ℕ} (I : Instance N M) (β : ℝ) (hβ : 0 < β) (τ : Allocation N M) (Y : Seeds N) (hY : unitSeeds Y) (i : Fin N) (hG : GenericOthers I β Y i) (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) (hlt : fUsed I β (Function.update Y i y) i < Bsum I β Y τ i y) : sumV I β Y τ i (fun v => if y ≤ v then (g β v - g β y) / (1 - g β y) else 0) ≤ fUsed I β (Function.update Y i y) i := by sorry

end UnknownBudgetAdwords
