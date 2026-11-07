-- Prove2me | Theorems.Thm_SelfCorrect3D_Memory_connected_subgraph_count
-- name    : SelfCorrect3D.Memory.connected_subgraph_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:30:46.161442+00:00
-- url     : https://prove2.me/theorems/a32657b9-5c77-47af-a328-4b045bfadb41
-- title:
--   Lemma 5.9 — at most $|V_2|(\Delta+1)^{2m}$ connected $m$-sets meeting $V_2$
-- statement:
--   Let $G$ be a finite simple graph in which every vertex has degree at most $\Delta$, let $V_2$ be a set of vertices and $m\in\mathbb N$. The number of $m$-element vertex sets $S$ that meet $V_2$ and induce a connected subgraph of $G$ satisfies
--
--   $$\#\{S:\ |S|=m,\ S\cap V_2\neq\emptyset,\ G[S]\text{ connected}\}\le |V_2|\,(\Delta+1)^{2m}.$$
--
--   In the paper, $G$ is the decoding graph and the witness subgraphs with $m$ nodes are among these sets; the bound controls the entropy term of the Peierls sum (233).
--
--   Differences from the source:
--   - generalization: witness subgraphs with m nodes of the decoding graph → all m-element vertex sets meeting V₂ that induce a connected subgraph, in any finite simple graph of maximum degree ≤ Δ; reason: a witness subgraph is a connected induced subgraph containing a node of G₂ (proof of Lemma 5.9: "it is sufficient for it to contain any v⁽²⁾ ∈ G₂"), so the count specializes
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, Lemma 5.9, p. 64 (decoding graph and Δ, p. 62)

import Mathlib

namespace SelfCorrect3D.Memory

open Classical in
/-- **Lemma 5.9 (counting witness subgraphs).** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, Lemma 5.9,
p. 64: "The number of witness subgraphs with m nodes is ≤ |V₂|(∆ + 1)^{2m}."

For every finite simple graph `G` of maximum degree at most `Δ`, every vertex set `V₂` and every
`m`, the number of `m`-element vertex sets `S` that meet `V₂` and induce a connected subgraph is at
most `|V₂| (Δ + 1)^{2m}`.

**Formalization Note (generalization).** A witness subgraph is a connected induced subgraph of the
decoding graph `G` (maximum degree `Δ`, p. 62) containing a node of `G₂` with vertex set `V₂`
(proof of Lemma 5.9: "it is sufficient for it to contain any v⁽²⁾ ∈ G₂"); the statement counts all
such sets, for any graph. `Δ = 0` is allowed. -/
theorem connected_subgraph_count {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ) (V₂ : Finset V) (m : ℕ) :
    (Finset.univ.filter fun S : Finset V =>
        S.card = m ∧ (S ∩ V₂).Nonempty ∧ (G.induce (S : Set V)).Connected).card ≤
      V₂.card * (Δ + 1) ^ (2 * m) := by sorry

end SelfCorrect3D.Memory
