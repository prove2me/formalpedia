-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_theorem_2
-- name    : UnknownBudgetAdwords.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:37.27836+00:00
-- url     : https://prove2.me/theorems/ca1f6867-e163-4972-ac70-fe22b89e7389
-- title:
--   Theorem 2: f-GPG is $0.522$-competitive at $\beta=1.15$ and $0.508$-competitive at $\beta=1$ (corrected: Algorithm 2 step)
-- statement:
--   For every instance of the budgeted allocation problem and every integral allocation $\tau$ with reward $\mathrm{OPT}$,
--
--   $$
--   E_Y[\text{f-GPG}(Y)]\ge0.522\,\mathrm{OPT}\quad\text{for }\beta=1.15,\qquad
--   E_Y[\text{f-GPG}(Y)]\ge0.508\,\mathrm{OPT}\quad\text{for }\beta=1.
--   $$
--
--   So f-GPG is at least $0.522$ competitive with $\beta=1.15$ and at least $0.508$ competitive with $\beta=1$, against the optimal integer offline allocation. Combined with Theorem 3 this gives the goal of the mission.
--
--   Differences from the source:
--   - correction: Algorithm 2 steps by δ_{i*}(t) = min{1, B_{i*}(t−1)/b_{i*,t}}, with the argmax over I(t) → each pass matches d = min(1 − δ, R_{i*}/b_{i*,t}), with the argmax over available resources with a positive bid; reason: on budgets (0.5, 10) and one arrival with bids (1, 1) the printed step matches 1.5 of one arrival, against "until t is fully (fractionally) matched" (p.10) and the continuous description of p.16; a zero bid would also be divided by
--   - encoding: "c competitive" against the optimal offline allocation → the inequality c · revenue I τ ≤ expected reward for every allocation τ; reason: there are finitely many allocations, so a bound for every τ is exactly a bound for the optimal one, and no division by OPT is needed; revenue is the capped reward of p.7, with r_i = 1 w.l.o.g. (p.7)
--   - encoding: no tie rule; ties have probability 0 (pp.9, 10) → ties are broken by least index; reason: the expectation does not depend on the rule
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Theorem 2, p.10

import Definitions.Def_UnknownBudgetAdwords_FGPG
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (seedAverage)
noncomputable section

namespace UnknownBudgetAdwords

/-- Theorem 2 (Udwani, arXiv:2110.00504v5, Theorem 2, p.10): with `β = 1.15`, f-GPG is at least
`0.522` competitive against the optimal (integer) offline allocation; with `β = 1` it is at least
`0.508` competitive.

**Formalization Note** Competitive means the inequality for every allocation `τ`, so for the
optimal one, with no division by `OPT`. -/
theorem theorem_2 {N M : ℕ} (I : Instance N M) (τ : Allocation N M) : 0.522 * revenue I τ ≤ seedAverage (fValue I 1.15) ∧ 0.508 * revenue I τ ≤ seedAverage (fValue I 1) := by sorry

end UnknownBudgetAdwords
