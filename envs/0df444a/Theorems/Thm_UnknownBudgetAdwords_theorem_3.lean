-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_theorem_3
-- name    : UnknownBudgetAdwords.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:34.557108+00:00
-- url     : https://prove2.me/theorems/80a69f16-c324-4056-bcce-9dca30d82f0d
-- title:
--   Theorem 3: a guarantee $\eta$ for f-GPG gives $\eta/(1+\gamma)$ for GPG (corrected: Algorithm 2 step)
-- statement:
--   Let $\beta>0$ and suppose that f-GPG with parameter $\beta$ has competitive ratio guarantee $\eta$, meaning that on every instance and for every allocation with reward $\mathrm{OPT}$, $E_Y[\text{f-GPG}(Y)]\ge\eta\,\mathrm{OPT}$. Then on every instance with bid-to-budget ratios at most $\gamma$, and for every allocation with reward $\mathrm{OPT}$,
--
--   $$
--   E_Y[\mathrm{GPG}(Y)]\ge\frac{\eta}{1+\gamma}\,\mathrm{OPT}.
--   $$
--
--   So GPG, with the same value of $\beta$, is $\frac{1}{1+\gamma}\eta$ competitive. The theorem turns a fractional algorithm that knows the budgets into a guarantee for an integral algorithm that does not.
--
--   **Formalization Note** The hypothesis is over all instances, because it is applied to the augmented instance.
--
--   Differences from the source:
--   - correction: Algorithm 2 steps by δ_{i*}(t) = min{1, B_{i*}(t−1)/b_{i*,t}}, with the argmax over I(t) → each pass matches d = min(1 − δ, R_{i*}/b_{i*,t}), with the argmax over available resources with a positive bid; reason: on budgets (0.5, 10) and one arrival with bids (1, 1) the printed step matches 1.5 of one arrival, against "until t is fully (fractionally) matched" (p.10) and the continuous description of p.16; a zero bid would also be divided by
--   - encoding: "c competitive" against the optimal offline allocation → the inequality c · revenue I τ ≤ expected reward for every allocation τ; reason: there are finitely many allocations, so a bound for every τ is exactly a bound for the optimal one, and no division by OPT is needed; revenue is the capped reward of p.7, with r_i = 1 w.l.o.g. (p.7)
--   - generalization: γ := max b_{i,t}/B_i (p.7) → any γ ≥ 0 with SmallBids I γ; reason: the printed γ is one such value, and a larger γ gives a weaker bound, so the statement specializes to the printed one
--   - encoding: no tie rule; ties have probability 0 (pp.9, 10) → ties are broken by least index; reason: the expectation does not depend on the rule
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Theorem 3, p.11

import Definitions.Def_UnknownBudgetAdwords_FGPG
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_SmallBids
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (seedAverage)
noncomputable section

namespace UnknownBudgetAdwords

/-- Theorem 3 (Udwani, arXiv:2110.00504v5, Theorem 3, p.11): given a competitive ratio guarantee
`η` for f-GPG with parameter `β`, GPG with the same `β` is `η / (1 + γ)` competitive.

**Formalization Note** The guarantee `hf` is over all instances of all sizes and all allocations:
its proof applies it to the augmented instance. `γ` is any bound on the bid-to-budget ratios
(`SmallBids I γ`); the paper's `γ = max b_{i,t} / B_i` is one, and a larger one gives a weaker
bound. -/
theorem theorem_3 (β η : ℝ) (hβ : 0 < β) (hf : ∀ (N' M' : ℕ) (J : Instance N' M') (σ : Allocation N' M'), η * revenue J σ ≤ seedAverage (fValue J β)) {N M : ℕ} (I : Instance N M) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : SmallBids I γ) (τ : Allocation N M) : η / (1 + γ) * revenue I τ ≤ seedAverage (gpgReward I β) := by sorry

end UnknownBudgetAdwords
