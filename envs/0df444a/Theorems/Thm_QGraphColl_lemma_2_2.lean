-- Prove2me | Theorems.Thm_QGraphColl_lemma_2_2
-- name    : QGraphColl.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:16.929663+00:00
-- url     : https://prove2.me/theorems/820f0a88-f44a-4b9e-9572-fb5f15a0f5f8
-- title:
--   Lemma 2.2 — counting marked volume: $\mathrm{vol}(G,S,x)=\sum_u|N_G(u)\cap S\cap M|$, additive over edge partitions
-- statement:
--   Let $G$ be a graph on the vertex set $V$ and $x$ an input with marked set $M$. For every $S\subseteq V$,
--   $$\mathrm{vol}(G,S,x)=\sum_{u\in V}|N_G(u)\cap S\cap M|.$$
--   Moreover, if the edge sets of graphs $G_1,\dots,G_t$ on the same vertex labels partition $E(G)$, then for every $S\subseteq V$
--   $$\mathrm{vol}(G,S,x)=\sum_{i=1}^{t}\mathrm{vol}(G_i,S,x).$$
--
--   Both identities count each edge once for each endpoint in $S\cap M$; the second is what makes marked volume additive over the pieces of an edge partition.
--
--   Differences from the source:
--   - encoding: the edge sets of G_1, …, G_t partition E(G) → the G_i are pairwise Disjoint graphs on V and ⨆ i, G_i = G; reason: in the lattice of simple graphs Disjoint means edge-disjoint and the supremum is the union of edge sets; same instances
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 2.2, p.13

import Mathlib
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol

namespace QGraphColl

/-- **Lemma 2.2** (Counting marked volume; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.13). For every `S ⊆ V(G)`,
`vol(G, S, x) = ∑_{u ∈ V(G)} |N_G(u) ∩ S ∩ M|`. If the edge sets of `G_1, …, G_t` partition
`E(G)`, then `vol(G, S, x) = ∑_i vol(G_i, S, x)`, retaining the same vertex labels.

**Formalization Note.** The pieces `G_i` are graphs on the same vertex type `V`; "the edge sets
partition `E(G)`" is: the `G_i` are pairwise edge-disjoint (`Disjoint` in the lattice of simple
graphs) and their supremum is `G`. Each `vol (Gs i) S x` uses degrees in `G_i`. -/
theorem lemma_2_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V → Bool) :
    (∀ S : Finset V, vol G S x = ∑ u, (nbr G u ∩ S ∩ marked x).card) ∧
    (∀ (t : ℕ) (Gs : Fin t → SimpleGraph V), Pairwise (fun i j => Disjoint (Gs i) (Gs j)) →
      (⨆ i, Gs i) = G → ∀ S : Finset V, vol G S x = ∑ i, vol (Gs i) S x) := by sorry

end QGraphColl
