-- Prove2me | Theorems.Thm_SeqPostedPricing_PartitionSPM_lemma_2_revenue_le_sum_price_prob
-- name    : SeqPostedPricing.PartitionSPM.lemma_2_revenue_le_sum_price_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:12:46.99295+00:00
-- url     : https://prove2.me/theorems/cec94cf5-cdb8-46b7-991e-4a7435100134
-- title:
--   Lemma 2: the revenue of a truthful mechanism is at most $\sum_i p_i^M q_i^M$
-- statement:
--   Let $n$ agents have independent values $v_i \sim F_i$, each $F_i$ regular with a density. Let $M$ be a mechanism that is truthful and individually rational (for almost every value profile) and serves a feasible set for some feasibility constraint, with measurable allocation events and integrable payments. Let $q_i^M$ be the probability that $M$ serves agent $i$, and for every agent with $q_i^M > 0$ let $p_i^M = F_i^{-1}(1 - q_i^M)$. Then
--
--   $$
--   R^M \le \sum_{i=1}^n p_i^M q_i^M .
--   $$
--
--   This is the upper bound against which the sequential posted-price mechanism is compared in every approximation result of the paper.
--
--   **Formalization Note** Agents with $q_i^M = 0$ contribute $0$ to the sum whatever their price.
--
--   Differences from the source:
--   - reading: any truthful mechanism M → any mechanism that is truthful and individually rational (`IsAdmissible`); reason: without individual rationality the bound is false (a mechanism that never serves and charges every agent 1 is truthful with revenue n > 0 = Σ p_i q_i); the paper's mechanisms are individually rational (Lemma 3, App. B)
--   - generalization: truthful (and individually rational) for the agents' possible values → truthful against every real misreport and individually rational for almost every value profile (`IsTruthful`, `IsIndividuallyRational`); reason: a mechanism truthful and individually rational on the supports of the values satisfies this (one defined only on reports in the supports is extended to all real reports by clamping each report to its support, an interval for regular laws), and profiles of probability 0 change neither R^M nor q_i^M
--   - encoding: q_i^M and the revenue of M → measurable allocation events and integrable payments (`IsAdmissible`); reason: the conditions only make q_i^M and the expected revenue defined
--   - generalization: a mechanism over the n agents → a mechanism that serves a feasible set for an arbitrary feasibility constraint Feas; reason: Feas = (every set feasible) is the paper's case
--   - reading: F_i regular (φ_i monotone non-decreasing), with density f_i → `IsRegular`: a density positive at every x with 0 < F_i(x) < 1 and φ_i monotone non-decreasing on that set; reason: φ_i is undefined where f_i = 0 and is read as −∞ there; monotonicity then forces a density positive strictly inside the support
--   - reading: p_i = F_i^{−1}(1 − q_i) → `IsQuantilePrice`: the largest p with Pr[v_i > p] = q_i; reason: unique for 0 < q_i < 1 under regularity; at q_i = 1 the bottom of the support (the inf convention would give −∞, not a price)
--   - encoding: p_i^M for every agent → p_i constrained only when q_i^M > 0; reason: the term p_i q_i^M is 0 when q_i^M = 0
--   - encoding: agents 1, …, n and an ordering σ → `Fin n` and σ : Fin n ≃ Fin n mapping the step to the agent offered at it; reason: Lean indexing convention; the same instances
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 2 (first sentence), p. 5 (PDF p. 7); proof in App. A, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsAdmissible
import Definitions.Def_SeqPostedPricing_PartitionSPM_revenue
import Definitions.Def_SeqPostedPricing_PartitionSPM_allocProb
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsRegular
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsQuantilePrice
import Definitions.Def_SeqPostedPricing_PartitionSPM_spmActive

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory

/-- **Lemma 2, first sentence** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 2, p. 5 = PDF p. 7; proof in App. A, p. 13 = PDF p. 15):
"If Fi is regular for each i, for any truthful mechanism M over the n agents, the revenue of M is
bounded from above by Σ_i p_i^M q_i^M where q_i^M is the probability (over v1, · · · , vn) with which
M allocates to agent i and p_i^M = F_i^{−1}(1 − q_i^M)."

For independent regular values and any admissible (feasible, truthful, individually rational,
measurable, integrable) mechanism `M`, `R^M ≤ Σ_i p_i q_i^M`, where `p_i` is the price
`F_i^{−1}(1 − q_i^M)` for every agent with `q_i^M > 0`.

**Formalization Note** "Truthful mechanism" is read as an admissible one (truthful and individually
rational; without individual rationality a mechanism that pays every agent loses revenue but not
truthfulness, and the bound is about expected revenue). Prices of agents with `q_i^M = 0` are
unconstrained; their term is `0`. Regularity is Reading 2, the quantile price Reading 3. -/
theorem lemma_2_revenue_le_sum_price_prob {n : ℕ} (Feas : Finset (Fin n) → Prop)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hreg : ∀ i, IsRegular (μ i))
    (M : Mechanism n) (hM : IsAdmissible Feas μ M)
    (p : Fin n → ℝ) (hp : ∀ i ∈ spmActive μ M, IsQuantilePrice (μ i) (allocProb μ M i) (p i)) :
    revenue μ M ≤ ∑ i, p i * allocProb μ M i := by sorry

end SeqPostedPricing.PartitionSPM
