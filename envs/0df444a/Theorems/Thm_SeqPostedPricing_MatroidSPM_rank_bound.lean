-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_rank_bound
-- name    : SeqPostedPricing.MatroidSPM.rank_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:40:34.056824+00:00
-- url     : https://prove2.me/theorems/b7d18410-f756-4c2a-acce-5c48a5f64853
-- title:
--   §4: $\sum_{i\in S}q_i^M\le\mathrm{rank}(S)$ for every set of agents
-- statement:
--   Let $\mathcal J$ be downward closed, let the values be independent, $v_i\sim\mu_i$, and let $M$ be a mechanism whose allocation $M(\mathbf v)$ is always feasible, with measurable allocation events. Then for every set $S\subseteq[n]$ of agents
--
--   $$
--   \sum_{i\in S}q_i^M\le\mathrm{rank}(S).
--   $$
--
--   It places the allocation probabilities of the benchmark mechanism inside the polytope of the constraint; the 2-approximation of Theorem 5 is proved for any probabilities with this property.
--
--   Differences from the source:
--   - encoding: Σ_{i∈S} q_i ≤ Σ_{i∈S} q_i^M ≤ rank(S) → Σ_{i∈S} q_i^M ≤ rank(S); reason: in §4 q_i = q_i^M (no point masses), so the first inequality is an equality
--   - generalization: q_i^M of Myerson's mechanism → q_i^M of any mechanism with feasible allocations and measurable allocation events; reason: the bound uses only that every allocation is feasible; Myerson's mechanism is such a mechanism
--   - encoding: probability that M serves agent i → measurable events {v | i ∈ M(v)}; reason: makes the probabilities countably additive; excludes no mechanism of the paper
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, unnumbered, p. 6

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_Mechanism
import Definitions.Def_SeqPostedPricing_MatroidSPM_allocProb
import Definitions.Def_SeqPostedPricing_MatroidSPM_rank
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **Rank bound: the allocation probabilities of a feasible mechanism sum to at most the rank on
every set of agents.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4, unnumbered, p. 6 (PDF p. 8): "Finally, let the rank of a subset S of agents, rank(S),
denote the size of the largest feasible subset in S, that is, rank(S) = max_{S′⊂S,S′∈J} |S′|.
Then, by definition, Σ_{i∈S} qi ≤ Σ_{i∈S} q_i^M ≤ rank(S)."

If `J` is downward closed (§2.1, p. 4) and the mechanism `M` always serves a feasible set, with
measurable allocation events, then for every set `S` of agents,
`Σ_{i∈S} q_i^M ≤ rank(S)`.

**Formalization Note.** In §4 `q_i = q_i^M` (the paper's mechanism has no point masses), so the
first inequality of the display is an equality and only the second is stated. Only downward
closure (the standing assumption of §2.1) is assumed, not the matroid axioms. -/
theorem rank_bound {n : ℕ} (Feas : Finset (Fin n) → Prop)
    (hdown : ∀ A B : Finset (Fin n), Feas A → B ⊆ A → Feas B)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (M : Mechanism n) (hfeas : ∀ v, Feas (M.alloc v))
    (hmeas : ∀ i, MeasurableSet {v : Fin n → ℝ | i ∈ M.alloc v}) (S : Finset (Fin n)) :
    ∑ i ∈ S, allocProb μ M i ≤ (rank Feas S : ℝ) := by sorry

end SeqPostedPricing.MatroidSPM
