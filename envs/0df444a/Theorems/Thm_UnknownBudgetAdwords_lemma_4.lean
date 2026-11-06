-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_lemma_4
-- name    : UnknownBudgetAdwords.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:11.666212+00:00
-- url     : https://prove2.me/theorems/e92578f1-23d0-466a-9b6b-12af2a284b76
-- title:
--   Lemma 4: bid prices are smallest in the base scenario (corrected: Algorithm 2 step)
-- statement:
--   Let $\beta>0$, let $i$ be a resource and $Y_{-i}$ seeds in $[0,1]$ for the others, without ties among themselves. For every $y_i\in[0,1]$, every arrival $t$ and every moment $\tau\in[t,t+1)$,
--
--   $$
--   \lambda_\tau(y_i)\ge\lambda_\tau(1)\ge b_{i,t}\big(1-g(y^c_{i,\tau})\big).
--   $$
--
--   Here $\lambda_\tau(y)$ is the bid price at the moment $\tau$ in f-GPG with seed $(y,Y_{-i})$. Both inequalities are part of the statement. Together they bound the bid prices of any run from below by those of the base scenario $y_i=1$, the first step in lower bounding $\theta_i+\sum_{t\in\mathrm{OPT}_i}\lambda_t$.
--
--   Differences from the source:
--   - correction: Algorithm 2 steps by δ_{i*}(t) = min{1, B_{i*}(t−1)/b_{i*,t}}, with the argmax over I(t) → each pass matches d = min(1 − δ, R_{i*}/b_{i*,t}), with the argmax over available resources with a positive bid; reason: on budgets (0.5, 10) and one arrival with bids (1, 1) the printed step matches 1.5 of one arrival, against "until t is fully (fractionally) matched" (p.10) and the continuous description of p.16; a zero bid would also be divided by
--   - reading: "given i ∈ I and seed Y_{−i}", with ties excluded in the proofs as having probability 0 (p.19) → the hypothesis GenericOthers I β Y i: no ties among resources other than i, and their seeds below 1; reason: the paper excludes ties in the proof; y_i stays free, since the lemma is for every y_i ∈ [0, 1]; ties_null shows the hypothesis holds almost surely
--   - encoding: moment τ ∈ [t, t+1) → the pair (t, s), s ∈ [0, 1), with availability read as positive remaining budget at the moment; reason: a resource exhausted exactly at τ is out at τ; this changes only single moments
--   - encoding: seeds Y ∈ [0,1]ⁿ → unitSeeds Y; reason: the same condition
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Lemma 4, p.17; proof in Appendix D, p.38

import Definitions.Def_UnknownBudgetAdwords_Thresholds
import Definitions.Def_UnknownBudgetAdwords_Generic
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds unitSeeds)
noncomputable section

namespace UnknownBudgetAdwords

/-- Lemma 4 (Udwani, arXiv:2110.00504v5, Lemma 4, p.17, proof in Appendix D, p.38): for every
`y_i ∈ [0, 1]`, arrival `t` and moment `τ = t + s`, `s ∈ [0, 1)`,
`λ_τ(y_i) ≥ λ_τ(1) ≥ b_{i,t} (1 − g(y^c_{i,τ}))`.

**Formalization Note** `Function.update Y i y` is the seed `(y, Y_{-i})`. The paper excludes ties
of probability 0 (p.19); `GenericOthers` excludes them among the resources other than `i`, and `y`
stays free. -/
theorem lemma_4 {N M : ℕ} (I : Instance N M) (β : ℝ) (hβ : 0 < β) (Y : Seeds N) (hY : unitSeeds Y) (i : Fin N) (hG : GenericOthers I β Y i) (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) (t : Fin M) (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) : lamAt I β (Function.update Y i 1) t s ≤ lamAt I β (Function.update Y i y) t s ∧ I.bid i t * (1 - g β (yc I β Y i t s)) ≤ lamAt I β (Function.update Y i 1) t s := by sorry

end UnknownBudgetAdwords
