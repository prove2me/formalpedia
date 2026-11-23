-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_Supplement_lemma_6
-- name    : SPPRevenue.SingleUnit.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:17:43.068394+00:00
-- url     : https://prove2.me/theorems/6a745bf8-1fd4-4a51-b480-6fa081d61bde
-- title:
--   Lemma 6 — the α-gap-weighted combination of optimal j-unit mechanisms is an optimal position auction
-- statement:
--   Consider the position-auction setting with click-through rates $1\ge\alpha_1\ge\dots\ge\alpha_n\ge0$, $\alpha_{n+1}=0$, and $n\ge1$ buyers with independent values $v_i\sim\mu_i$. For $j\in[n]$ let $(x^j,\pi^j)$ be an optimal truthful, individually rational mechanism for $j$ units, with allocations $x^j_i(v)\in\{0,1\}$ and payments $\pi^j_i(v)\ge0$. Then the mechanism
--   $$x_i(v)=\sum_{j\in[n]}(\alpha_j-\alpha_{j+1})x^j_i(v),\qquad \pi_i(v)=\sum_{j\in[n]}(\alpha_j-\alpha_{j+1})\pi^j_i(v)$$
--   is an optimal truthful, individually rational mechanism for the position auction: its expected clicks are feasible at every reported profile, and no truthful, individually rational position-auction mechanism earns more.
--
--   It reduces the position auction to the multi-unit auctions and gives the decomposition $\mathbb E[\sum_i\pi_i]=\sum_j(\alpha_j-\alpha_{j+1})\mathbb E[\sum_i\pi^j_i]$ used in Theorem 4.
--
--   **Formalization Note** Truthfulness is the interim condition of p. 21, for all real values and reports, with interim individual rationality; total revenue can be infinite and is compared in the extended reals; feasibility is required at every reported profile; expected clicks are feasible when produced by a randomized assignment of buyers to positions.
--
--   Differences from the source:
--   - generalization: x^j, π^j are the j-unit optimal (Myerson) mechanisms, which are nested (a buyer allocated with j units is allocated with j′ > j units), for atomless or finitely supported value laws → any family of optimal j-unit mechanisms with 0/1 allocations and nonnegative payments, not assumed nested, for arbitrary value laws; reason: the aggregate's clicks are feasible by Lemmas 5 and 7 without nesting, and the revenue bound is the same; the source's nested family is such a family
--   - reading: truthful mechanism, optimal mechanism → IsTruthfulIR: measurable allocations and payments, integrable at every fixed report for interim expectations; defined signed extended individual expected payments and total revenue; pointwise feasibility; interim IC/IR for all real values and reports. IsOptimal compares signed extended revenues in that class; reason: the source expectations and pointwise feasible mechanisms on pp. 9, 20–21, including infinite expected revenues; only undefined ∞−∞ expectations are excluded
--   - encoding: positions and units j ∈ [n], α_{n+1} = 0 → index j : Fin n is the paper's j + 1; ctrGap α j = α_j − α_{j+1} with α_{n+1} = 0; 1 ≤ n; reason: Lean indexing; the gaps are those of the source
--   - encoding: randomized allocation y ∈ [0,1]^{|A|} → a probability vector on maps from buyers to optional positions, supported on maps assigning each position at most once; reason: the same set of randomized allocations
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 22, Lemma 6; proof §8.6, pp. 40–41

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Mechanism
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Position

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory

theorem lemma_6 {n : ℕ} (hn : 1 ≤ n) (α : Fin n → ℝ) (hα : IsCTR α) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (M : Fin n → DirectMech n)
    (hopt : ∀ j : Fin n, IsOptimal μ (UnitFeasible ((j : ℕ) + 1)) (M j))
    (halloc : ∀ j v i, (M j).alloc v i = 0 ∨ (M j).alloc v i = 1)
    (hpay : ∀ j v i, 0 ≤ (M j).pay v i) :
    IsOptimal μ (PAFeasibleClicks α) (paMech α M) := by sorry

end SPPRevenue.SingleUnit.Supplement
