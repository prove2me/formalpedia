-- Prove2me | Theorems.Thm_SkewMatching_expander_cut_sampling
-- name    : SkewMatching.expander_cut_sampling
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:45.519697+00:00
-- url     : https://prove2.me/theorems/37f8fcd0-b10a-4562-ae0a-1c6c8132b841
-- title:
--   §3.6, p.12 — one trial outputs each cut edge with probability exactly w_e/Z and accepts with probability at least ϕ/2
-- statement:
--   Let $A_1,\dots,A_r$ be edge-disjoint loopless unweighted graphs on a vertex set $V$ with edge weights $w_e\in(2^{j_i-1},2^{j_i}]$ on $A_i$, let $S\subseteq V$, and suppose
--
--   $$
--   Z=\sum_i 2^{j_i}\min\{\mathrm{vol}_{A_i}(S),\mathrm{vol}_{A_i}(V\setminus S)\}>0.
--   $$
--
--   Then:
--
--   1. one trial of the sampling step outputs each edge $e\in\partial S$ of the family with probability exactly $w_e/Z$, and outputs no edge outside $\partial S$;
--   2. if every $A_i$ is a $\phi$-expander, the trial outputs some edge with probability at least $\phi/2$.
--
--   This is the sampling step of the cut-sampling data structure. Repeating the trial gives an edge of $\partial S$ with probability exactly proportional to its weight, in expected $2/\phi$ repeats.
--
--   Differences from the source:
--   - reading: a choice of expander, then a vertex, then an edge, with rejection → the explicit product formula ExpanderFamily.trialProb; reason: the output probability of one trial is this product; the paper states the steps in words
--   - reading: the probability is at least 2^{−O(log^{3/4} n)} → at least φ/2 for a family of φ-expanders; reason: the decomposition of p.12 has φ = 2^{−O(log^{3/4} n)}; its construction is the cited Theorem 19, not posed here
--   - reading: B is the smaller side of the cut → on a tie, B is V \ S; reason: p.12 does not break ties and p.11 uses V \ S; with equal volumes either side gives the same output probabilities
--   - encoding: volumes and cuts within the support U of A → volumes and cuts over all of V; reason: vertices off the support have degree 0, so the values agree
--   - generalization: the expanders of the dynamic decomposition → any finite family of edge-disjoint φ-expanders with weights in the stated ranges; reason: the argument uses only these properties, and the paper's family is one such
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), §3.6, proof of Lemma 16, pp.11–12

import Mathlib
import Definitions.Def_SkewMatching_ExpanderFamily

namespace SkewMatching

open scoped Classical

/-- **Sampling step**, §3.6, proof of Lemma 16, p.12. "For sampling, we first sample an expander A (of vertex support U) with probability proportional to its weight 2^j min{vol_A(U ∩ S), vol_A(U \ S)}, where j is the index of the graph G_j that contains A. Next, supposing that B is the smaller side of the cut U ∩ S and U \ S, we sample a vertex v from B with
probability proportional to its degree deg_A(v) in A, and then sample an edge adjacent to v in A. If this edge is not in the cut ∂S, we reject it and repeat; If this edge is in ∂S, we also reject and repeat with probability 1 − w_e/2^j ≤ 1/2."

One trial outputs each edge `e` of `∂S` with probability exactly `w_e / Z`, and no other edge, and if every `A_i` is a `ϕ`-expander, a trial accepts with probability at least `ϕ/2`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), §3.6, p.12.

**Formalization Note.** The bound `2^{−O(log^{3/4} n)}` of p.12 is `ϕ/2` for the expanders of the decomposition, whose construction (Theorem 19) is cited and is not posed. The trial's probability is the explicit product formula `ExpanderFamily.trialProb`, and `Z > 0` is the case where sampling is defined. `min`,
`vol` over all `V` agree with the support `U`, since vertices off the support have degree `0`. -/
theorem expander_cut_sampling {V E ι : Type*} [Fintype V] [Fintype E] [Fintype ι]
    (F : ExpanderFamily V E ι) (S : Finset V) (hZ : 0 < F.totalWeight S) :
    (∀ i, ∀ e ∈ F.edges i, F.trialProb S e = if F.InCut S e then F.weight e / F.totalWeight S else 0) ∧
      ∀ φ : ℝ, (∀ i, F.IsExpander φ i) →
        φ / 2 ≤ ∑ e ∈ Finset.univ.biUnion F.edges, F.trialProb S e := by sorry

end SkewMatching
