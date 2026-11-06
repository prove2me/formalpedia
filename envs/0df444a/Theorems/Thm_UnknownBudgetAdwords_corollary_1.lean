-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_corollary_1
-- name    : UnknownBudgetAdwords.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:47.974902+00:00
-- url     : https://prove2.me/theorems/0d8d7775-765f-42f3-b1d6-fa6e7b5adbeb
-- title:
--   Corollary 1: GPG is $0.522/(1+\gamma)$-competitive at $\beta=1.15$ and $0.508/(1+\gamma)$-competitive at $\beta=1$
-- statement:
--   For every instance of the budgeted allocation problem, with budgets $B_i>0$ and bids $b_{i,t}\ge0$, every $\gamma\ge0$ with $b_{i,t}\le\gamma B_i$ for all $i,t$, and every integral allocation with capped reward $\mathrm{OPT}$,
--
--   $$
--   E_Y[\mathrm{GPG}(Y)]\ge\frac{0.522}{1+\gamma}\,\mathrm{OPT}\quad\text{for }\beta=1.15,\qquad
--   E_Y[\mathrm{GPG}(Y)]\ge\frac{0.508}{1+\gamma}\,\mathrm{OPT}\quad\text{for }\beta=1,
--   $$
--
--   where the expectation is over seeds i.i.d. uniform on $[0,1]$.
--
--   Thus Generalized Perturbed Greedy, which never reads a budget, is at least $\frac{1}{1+\gamma}0.522$ competitive for $\beta=1.15$ and at least $\frac{1}{1+\gamma}0.508$ competitive for $\beta=1$. These results hold for any instance, for arbitrary $\gamma$: bids may exceed budgets. For small bids, $\gamma\to0$, the ratio is strictly better than the $0.5$ that deterministic budget-oblivious algorithms cannot beat.
--
--   Differences from the source:
--   - encoding: "c competitive" against the optimal offline allocation → the inequality c · revenue I τ ≤ expected reward for every allocation τ; reason: there are finitely many allocations, so a bound for every τ is exactly a bound for the optimal one, and no division by OPT is needed; revenue is the capped reward of p.7, with r_i = 1 w.l.o.g. (p.7)
--   - generalization: γ := max b_{i,t}/B_i (p.7) → any γ ≥ 0 with SmallBids I γ; reason: the printed γ is one such value, and a larger γ gives a weaker bound, so the statement specializes to the printed one
--   - encoding: no tie rule; ties have probability 0 (pp.9, 10) → ties are broken by least index; reason: the expectation does not depend on the rule
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Corollary 1, p.11

import Definitions.Def_UnknownBudgetAdwords_GPG
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_SmallBids
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (seedAverage)
noncomputable section

namespace UnknownBudgetAdwords

/-- Corollary 1 (Udwani, arXiv:2110.00504v5, Corollary 1, p.11): for `β = 1.15`, GPG is at least
`0.522 / (1 + γ)` competitive; for `β = 1`, GPG is at least `0.508 / (1 + γ)` competitive.

**Formalization Note** Competitive means the inequality for every allocation `τ`, so for the
optimal one, with no division by `OPT`. It holds for every instance, "for arbitrary value of γ"
(p.11): `γ` is any bound on the bid-to-budget ratios, and bids may exceed budgets. The expectation
is over the seeds, i.i.d. uniform on `[0, 1]`. -/
theorem corollary_1 {N M : ℕ} (I : Instance N M) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : SmallBids I γ) (τ : Allocation N M) : 0.522 / (1 + γ) * revenue I τ ≤ seedAverage (gpgReward I 1.15) ∧ 0.508 / (1 + γ) * revenue I τ ≤ seedAverage (gpgReward I 1) := by sorry

end UnknownBudgetAdwords
