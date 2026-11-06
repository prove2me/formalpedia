-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_lemma_3
-- name    : UnknownBudgetAdwords.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:10.632218+00:00
-- url     : https://prove2.me/theorems/5866fa9f-d9ba-4ac3-bbd7-0729f1287605
-- title:
--   Lemma 3: the conditional bound (7) implies (2) (corrected: Algorithm 2 step)
-- statement:
--   Let $\beta>0$, let $i$ be a resource, let $\tau$ be an allocation with reward $\mathrm{OPT}_i$ on $i$, and let $\alpha>0$. Suppose that for the candidate solution (6),
--
--   $$
--   E_{y_i}\Big[\theta_i(Y)+\sum_{t\in\mathrm{OPT}_i}\lambda_t(Y)\ \Big|\ Y_{-i}\Big]\ge\alpha\,\mathrm{OPT}_i
--   $$
--
--   for almost every $Y_{-i}\in[0,1]^{n-1}$. Then inequality (2) holds for $i$ with the same $\alpha$:
--
--   $$
--   \theta_i+\sum_{t\in\mathrm{OPT}_i}\lambda_t\ge\alpha\,\mathrm{OPT}_i.
--   $$
--
--   This reduces the proof of (2) to a statement about one seed with the others fixed.
--
--   **Formalization Note** The conditional expectation is `oneSeedAverage i Y`, the integral over $y_i\in[0,1]$ of the seed vector with its $i$-th coordinate replaced.
--
--   Differences from the source:
--   - correction: Algorithm 2 steps by δ_{i*}(t) = min{1, B_{i*}(t−1)/b_{i*,t}}, with the argmax over I(t) → each pass matches d = min(1 − δ, R_{i*}/b_{i*,t}), with the argmax over available resources with a positive bid; reason: on budgets (0.5, 10) and one arrival with bids (1, 1) the printed step matches 1.5 of one arrival, against "until t is fully (fractionally) matched" (p.10) and the continuous description of p.16; a zero bid would also be divided by
--   - encoding: no tie rule; ties have probability 0 (pp.9, 10) → ties are broken by least index; reason: the expectation does not depend on the rule
--   - generalization: (7) for every Y_{−i} ∈ [0,1]^{n−1} → (7) for almost every Y under the seed law; reason: a weaker hypothesis gives a stronger lemma, and it is what Lemma 6 supplies off the tie set; the printed hypothesis implies it
--   - generalization: OPT_i, the optimal offline allocation → τ any allocation; reason: the proof uses only feasibility of OPT, so the statement specializes to τ optimal
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Lemma 3, p.16

import Definitions.Def_UnknownBudgetAdwords_FGPG
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (seedLaw seedAverage oneSeedAverage)
open MeasureTheory
noncomputable section

namespace UnknownBudgetAdwords

/-- Lemma 3 (Udwani, arXiv:2110.00504v5, Lemma 3, p.16): if the conditional bound (7),
`E_{y_i}[θ_i(Y) + ∑_{t ∈ OPT_i} λ_t(Y) | Y_{-i}] ≥ α OPT_i`, holds, then inequality (2) holds for
resource `i` with the same `α`.

**Formalization Note** `oneSeedAverage i Y f` integrates `f` over `y_i ∈ [0, 1]` with the other
seeds of `Y` fixed. (7) is assumed for almost every seed rather than for all: a weaker hypothesis,
which is what Lemma 6 supplies off the set of ties. `OPT_i` is the reward of the allocation `τ` on
`i`. -/
theorem lemma_3 {N M : ℕ} (I : Instance N M) (β : ℝ) (hβ : 0 < β) (τ : Allocation N M) (i : Fin N) (α : ℝ) (hα : 0 < α) (h7 : ∀ᵐ Y ∂seedLaw N, α * spend I τ i M ≤ oneSeedAverage i Y (fun Y' => theta I β Y' i + ∑ t ∈ Finset.univ.filter (fun t => τ t = some i), lam I β Y' t)) : α * spend I τ i M ≤ seedAverage (fun Y => theta I β Y i) + ∑ t ∈ Finset.univ.filter (fun t => τ t = some i), seedAverage (fun Y => lam I β Y t) := by sorry

end UnknownBudgetAdwords
