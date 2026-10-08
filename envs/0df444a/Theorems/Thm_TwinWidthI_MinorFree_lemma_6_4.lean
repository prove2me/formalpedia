-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_lemma_6_4
-- name    : TwinWidthI.MinorFree.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:24.470992+00:00
-- url     : https://prove2.me/theorems/00a64edd-e44b-48d2-a849-cc2af4e6b5dd
-- title:
--   Lemma 6.4 — the vertices a_{i,j} lie on a single branch of the DFS tree
-- statement:
--   Let $(v_1,\dots,v_n;\mathcal T)$ be a depth-first search of a finite graph $G$, and let $k\ge 0$. Suppose vertices $a_{i,j}$ and $b_{i,j}$ ($i,j\in[k]$) satisfy:
--
--   1. $a_{i,j}b_{i,j}$ is an edge of $G$ for all $i,j$;
--   2. $a_{i,j}\prec a_{i',j'}$ in the discovery order whenever $i<i'$;
--   3. $a_{i,j}\prec b_{i',j'}$ for all $i,j,i',j'$.
--
--   Then any two of the $a_{i,j}$ are in ancestor–descendant relation in $\mathcal T$: if $a_{i,j}\preccurlyeq a_{i',j'}$, then $a_{i,j}$ is an ancestor of $a_{i',j'}$,
--
--   $$
--   a_{i,j}\preccurlyeq a_{i',j'}\ \Longrightarrow\ a_{i,j}\ \text{is an ancestor of}\ a_{i',j'} .
--   $$
--
--   So all the $a_{i,j}$ lie on a single branch, first $\bigcup_j\{a_{1,j}\}$, then $\bigcup_j\{a_{2,j}\}$, and so on.
--
--   In the proof of Theorem 6.3, $k=g(t)/2$, $a_{i,j}\in A_i$ and $b_{i,j}\in B_j$, where $A_1,\dots,A_k$ are consecutive blocks of the discovery order preceding the consecutive blocks $B_1,\dots,B_k$; the lemma lets the paper contract the paths $A'_i$ into the branch sets of a minor. As the paper notes, only the definition of a DFS is used, not the Lex-DFS tie-break.
--
--   **Formalization Note** Hypotheses 1–3 are exactly the properties of the proof's vertices that the lemma uses; the blocks $A_i,B_j$ themselves are not needed. The "In particular" clause (the minimal subtrees $A'_i$ are pairwise-disjoint paths) is not stated separately.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:27, Lemma 6.4 (context p. 3:26, proof of Theorem 6.3)

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_LexDFS

namespace TwinWidthI.MinorFree

/-- Lemma 6.4, p. 3:27. In a DFS (`σ`, `par`) of `G`, let `a i j` (`i, j < k`, the paper's
`a_{i+1,j+1} ∈ A_{i+1}`) be vertices with a neighbour `b i j` (`∈ B_{j+1}`), such that every
`a i j` is discovered before every `a i' j'` with `i < i'` (the `A_i` are consecutive blocks in
this order) and before every `b i' j'` (all of `⋃ A_i` precedes `⋃ B_j`). Then all the `a i j`
lie on a single branch of the DFS tree: an earlier one is an ancestor of a later one. -/
theorem lemma_6_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) {k : ℕ}
    (a b : Fin k → Fin k → V) (hab : ∀ i j, G.Adj (a i j) (b i j))
    (ha : ∀ i j i' j', i < i' → σ (a i j) < σ (a i' j'))
    (hb : ∀ i j i' j', σ (a i j) < σ (b i' j')) :
    ∀ i j i' j', σ (a i j) ≤ σ (a i' j') → IsAncestor par (a i j) (a i' j') := by sorry

end TwinWidthI.MinorFree
