-- Prove2me | Theorems.Thm_SeqPostedPricing_PartitionSPM_rank_bound
-- name    : SeqPostedPricing.PartitionSPM.rank_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:13:27.367432+00:00
-- url     : https://prove2.me/theorems/9d1dd007-1925-437c-8713-c97b09453048
-- title:
--   Rank bound: $\sum_{i\in S} q_i^M \le \mathrm{rank}(S)$
-- statement:
--   Let $\mathcal J$ be a downward-closed feasibility constraint on $n$ agents, let the values be independent with laws $\mu_i$, and let $M$ be a mechanism that always serves a feasible set and whose allocation events are measurable. Then for every set $S$ of agents
--
--   $$
--   \sum_{i \in S} q_i^M \le \mathrm{rank}(S),
--   $$
--
--   where $\mathrm{rank}(S)$ is the size of the largest feasible subset of $S$.
--
--   In the analysis of the mechanism $\mathcal S$ (which uses $q_i = q_i^M$) this bounds the total acceptance probability of every set of agents by its rank; for a block of a partition matroid it gives $\sum_{i \in \text{block}} q_i \le \text{capacity}$.
--
--   Differences from the source:
--   - encoding: Σ_{i∈S} q_i ≤ Σ_{i∈S} q_i^M ≤ rank(S) → Σ_{i∈S} q_i^M ≤ rank(S); reason: the mechanism S uses q_i = q_i^M, so the first inequality is an equality
--   - reading: rank(S) = max_{S′⊂S, S′∈J} |S′| → maximum over S′ ⊆ S; reason: the largest feasible subset may be S itself
--   - generalization: Myerson's mechanism with regular value distributions → any mechanism with feasible allocations and measurable allocation events, any value laws; reason: the bound uses only feasibility of the allocation; Myerson's mechanism with regular laws is a special case
--   - encoding: the standing assumption that J is downward closed (§2.1) → hypothesis hdown; reason: the paper's standing assumption
--   - encoding: agents 1, …, n and an ordering σ → `Fin n` and σ : Fin n ≃ Fin n mapping the step to the agent offered at it; reason: Lean indexing convention; the same instances
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, unnumbered, p. 6 (PDF p. 8)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_Mechanism
import Definitions.Def_SeqPostedPricing_PartitionSPM_allocProb
import Definitions.Def_SeqPostedPricing_PartitionSPM_rank

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory

/-- **Rank bound** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, unnumbered, p. 6 = PDF p. 8): "Finally, let the rank of a subset S of
agents, rank(S), denote the size of the largest feasible subset in S, that is,
rank(S) = max_{S′⊂S,S′∈J} |S′|. Then, by definition, Σ_{i∈S} qi ≤ Σ_{i∈S} q_i^M ≤ rank(S)."

For a downward-closed set system `J` (§2.1, p. 4) and a mechanism that always serves a feasible
set, with measurable allocation events, `Σ_{i ∈ S} q_i^M ≤ rank(S)` for every set `S` of agents.

**Formalization Note** The paper's first inequality `Σ_{i∈S} q_i ≤ Σ_{i∈S} q_i^M` is an equality
here, since the mechanism S uses `q_i = q_i^M`. Downward closure is the standing assumption of
§2.1 ("We assume that the set system J is downward closed"). -/
theorem rank_bound {n : ℕ} (Feas : Finset (Fin n) → Prop)
    (hdown : ∀ A B : Finset (Fin n), A ⊆ B → Feas B → Feas A)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (M : Mechanism n) (hfeas : ∀ v, Feas (M.alloc v))
    (hmeas : ∀ i, MeasurableSet {v | i ∈ M.alloc v}) (S : Finset (Fin n)) :
    ∑ i ∈ S, allocProb μ M i ≤ (rank Feas S : ℝ) := by sorry

end SeqPostedPricing.PartitionSPM
