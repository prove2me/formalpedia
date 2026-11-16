-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_Supplement_lemma_5_2
-- name    : SortingCounterexamples.Optimal.Supplement.lemma_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:37:09.308075+00:00
-- url     : https://prove2.me/theorems/5175a9ef-fd31-498e-b0a2-4483ab3cfabb
-- title:
--   Lemma 5.2 — the strong-majority graph $G_t$ of a $d$-dimensional geometric class is acyclic
-- statement:
--   Let $v_1,\dots,v_n\in\mathbb R^d$ and let $H$ be a finite class of rankings of the $n$ items such that every $\pi\in H$ is induced by some direction $w\in\mathbb R^d$ ($i\prec_\pi j\iff\langle v_i,w\rangle<\langle v_j,w\rangle$). For any transcript of queries and returned pairs, let $q(\pi)$ be the weighted-majority weights (halved on every round in which $\pi$ agrees with the query on the returned pair), $P(\pi)=q(\pi)/\sum_{\pi'\in H}q(\pi')$, and $p(i,j)=\Pr_{\Pi\sim P}[i\prec_\Pi j]$. Let $G$ be the directed graph on the items with an edge $i\to j$ for distinct $i,j$ whenever
--   $$p(i,j)>1-\frac1{d+1}.$$
--   Then $G$ has no directed cycle.
--
--   This is the geometric fact behind the upper bound of Theorem 5.1: a sufficiently strong weighted majority of a $d$-dimensional geometric class can be completed to a linear order.
--
--   **Formalization Note** Acyclicity is stated as: no item $i$ is related to itself by the transitive closure of the edge relation.
--
--   Differences from the source:
--   - generalization: G_t for the weights at time t of the algorithm → G for the weights after any transcript (any sequence of queries and returned pairs); reason: the weights q_t of the algorithm are the weights of its own transcript, so the source's statement is the special case of transcripts produced by the learner
--   - encoding: G_t is acyclic → ¬ TransGen (MajorityEdge d H h) i i for every item i; reason: a directed cycle exists exactly when some item reaches itself along edges
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 23 / PDF p. 24, Lemma 5.2 with eq. (8) (proof to printed p. 24 / PDF p. 25); setting printed p. 22 / PDF p. 23, §5 and proof of Theorem 5.1

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol
import Definitions.Def_SortingCounterexamples_Optimal_Supplement_Geometric

namespace SortingCounterexamples.Optimal.Supplement

open SortingCounterexamples.Optimal

/-- Lemma 5.2: for a `d`-dimensional geometric class `H` with representation `v` and the
weights after any transcript `h`, the strong-majority graph `G_t` (edges `i → j` with
`p_t(i, j) > 1 - 1/(d+1)`) has no directed cycle. -/
theorem lemma_5_2 {n d : ℕ} (v : Fin n → Fin d → ℝ) (H : Finset (Ranking n))
    (hH : IsGeometricClass v H) (h : Transcript n) :
    ∀ i : Fin n, ¬ Relation.TransGen (MajorityEdge d H h) i i := by sorry

end SortingCounterexamples.Optimal.Supplement
