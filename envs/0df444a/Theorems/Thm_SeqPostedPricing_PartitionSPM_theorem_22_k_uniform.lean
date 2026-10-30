-- Prove2me | Theorems.Thm_SeqPostedPricing_PartitionSPM_theorem_22_k_uniform
-- name    : SeqPostedPricing.PartitionSPM.theorem_22_k_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:16:58.079953+00:00
-- url     : https://prove2.me/theorems/2cad2da9-51e5-4849-8de3-d6b0777752c2
-- title:
--   Theorem 22: the SPM $\mathcal S$ is an $e/(e-1)$-approximation for a $k$-uniform matroid
-- statement:
--   Let $n$ agents have independent values $v_i \sim F_i$, each $F_i$ regular with a density. Let the feasibility constraint be the $k$-uniform matroid (at most $k$ agents are served), for any $k \in \mathbb N$. Let $M$ be a revenue-optimal mechanism for this constraint (for instance Myerson's mechanism), and let $q_i = q_i^M$ be the probability that $M$ serves agent $i$. Let $\mathcal S$ be the **sequential posted-price mechanism** that offers each agent $i$ with $q_i > 0$ the price
--
--   $$
--   p_i = F_i^{-1}(1 - q_i),
--   $$
--
--   in decreasing order of the prices (ties broken arbitrarily), serving an agent when it accepts and the served set stays feasible. Then
--
--   $$
--   R^M \le \frac{e}{e-1}\, R^{\mathcal S}.
--   $$
--
--   **Formalization Note** An agent accepts its offer when $p_i \le v_i$. The order is a bijection from steps to agents.
--
--   Differences from the source:
--   - generalization: Myerson's mechanism, with S built from its service probabilities q_i^M → any optimal admissible mechanism M (`IsOptimal`), with S built from M's service probabilities; reason: Myerson's mechanism is deterministic, truthful and individually rational at every profile (so for almost every profile), feasible, has measurable allocation events and integrable payments, and is optimal by Theorem 19, so the paper's statement is the special case
--   - reading: F_i regular (φ_i monotone non-decreasing), with density f_i → `IsRegular`: a density positive at every x with 0 < F_i(x) < 1 and φ_i monotone non-decreasing on that set; reason: φ_i is undefined where f_i = 0 and is read as −∞ there; monotonicity then forces a density positive strictly inside the support
--   - reading: p_i = F_i^{−1}(1 − q_i) → `IsQuantilePrice`: the largest p with Pr[v_i > p] = q_i; reason: unique for 0 < q_i < 1 under regularity; at q_i = 1 the bottom of the support (the inf convention would give −∞, not a price)
--   - encoding: every agent is offered its price and accepts with probability exactly q_i → only agents with q_i > 0 are offered (`spmActive`); prices of the others are unconstrained; reason: an agent with q_i = 0 accepts with probability 0, so the outcome is the same almost surely
--   - encoding: a rational agent accepts iff the price is no more than its value → acceptance is p_i ≤ v_i; reason: the paper's rule (§1); with a density Pr[v_i ≥ p_i] = 1 − F_i(p_i) = q_i
--   - generalization: the agents are offered in decreasing order of their prices → any order σ that is non-increasing in price over the offered agents (`IsDecreasingOrder`); reason: the paper fixes no tie-break; every tie-break of the decreasing order is covered
--   - encoding: agents 1, …, n and an ordering σ → `Fin n` and σ : Fin n ≃ Fin n mapping the step to the agent offered at it; reason: Lean indexing convention; the same instances
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Theorem 22, p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_uniformFeasible
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsOptimal
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsRegular
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsQuantilePrice
import Definitions.Def_SeqPostedPricing_PartitionSPM_spmRevenue
import Definitions.Def_SeqPostedPricing_PartitionSPM_spmActive
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsDecreasingOrder

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory

/-- **Theorem 22** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Theorem 22, p. 15 = PDF p. 17): "The revenue R^S of the SPM S is a e/(e−1) approximation to the
expected revenue of Myerson's mechanism in the case of a k-uniform matroid."

For independent regular values and the `k`-uniform matroid (at most `k` agents served), for every `k : ℕ`, let `M` be an optimal admissible mechanism with
service probabilities `q_i`, and let S be the SPM that offers the agents with `q_i > 0` the prices
`p_i = F_i^{−1}(1 − q_i)` in decreasing order of price. Then `R^M ≤ e/(e − 1) · R^S`.

**Formalization Note** The mechanism S of §4 is the SPM that offers only the agents served by `M` with positive
probability (`spmActive`, Reading 4), with prices `p_i = F_i^{−1}(1 − q_i)` (`IsQuantilePrice`,
Reading 3) and any order that is non-increasing in price (`IsDecreasingOrder`, Reading 6).
"Myerson's mechanism" is any optimal admissible mechanism `M` (`IsOptimal`, Reading 1); regularity
is `IsRegular` (Reading 2); acceptance is `p_i ≤ v_i` (Reading 5). Agents are `Fin n`; `σ` maps the
step to the agent. -/
theorem theorem_22_k_uniform {n : ℕ} (k : ℕ)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hreg : ∀ i, IsRegular (μ i))
    (M : Mechanism n) (hM : IsOptimal (uniformFeasible k) μ M)
    (p : Fin n → ℝ) (hp : ∀ i ∈ spmActive μ M, IsQuantilePrice (μ i) (allocProb μ M i) (p i))
    (σ : Fin n ≃ Fin n) (hσ : IsDecreasingOrder p (spmActive μ M) σ) :
    revenue μ M ≤ Real.exp 1 / (Real.exp 1 - 1) *
      spmRevenue (uniformFeasible k) μ p (spmActive μ M) σ := by sorry

end SeqPostedPricing.PartitionSPM
