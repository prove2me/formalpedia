-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_lemma_6_5
-- name    : TwinWidthI.MinorFree.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:42.268985+00:00
-- url     : https://prove2.me/theorems/8f8c5df3-252d-43f2-a68c-e07d764f51c9
-- title:
--   Lemma 6.5 (corrected) — the enhancements B*_j avoid the paths A′_i, except the last ones
-- statement:
--   Let $(v_1,\dots,v_n;\mathcal T)$ be a depth-first search of a finite graph $G$ and let $k\ge0$. Let $a_{i,j}$, $b_{i,j}$ ($i,j\in[k]$) be vertices and $B_1,\dots,B_k$ vertex sets such that:
--
--   1. $a_{i,j}b_{i,j}$ is an edge of $G$, and $b_{i,j}\in B_j$;
--   2. $a_{i,j}\prec a_{i',j'}$ whenever $i<i'$;
--   3. each $B_j$ is consecutive in the discovery order, and $B_j$ entirely precedes $B_{j'}$ when $j<j'$;
--   4. every vertex of every $B_{j'}$ comes after every $a_{i,j}$.
--
--   Let $A'_i$ be the vertex set of the minimal subtree of $\mathcal T$ containing $\{a_{i,j}:j\in[k]\}$, and $B^*_j$ that of the minimal subtree containing $B_j$ (the **enhancement** of $B_j$). Then
--
--   $$
--   B^*_j\cap A'_i=\emptyset\qquad\text{for all } i\in[k-1],\ j\in[k-1].
--   $$
--
--   In the proof of Theorem 6.3 ($k=g(t)/2$) this lets each enhancement be contracted without destroying the paths $A'_i$.
--
--   **Formalization Note** The paper states the lemma for every $j\in[g(t)/2]$. For the last block it can fail: the proof's claim that every $B_j$ lies in the subtree $\mathcal T[u]$, $u$ the first vertex of $A'_{g(t)/2}$, holds for the blocks before $B_{g(t)/2}$ (they are discovered between $u$ and $b_{g(t)/2,g(t)/2}\in\mathcal T[u]$) but not for vertices of $B_{g(t)/2}$ discovered after $\mathcal T[u]$ is exhausted. A five-vertex DFS (which is also a Lex-DFS) satisfying all hypotheses with $B^*_2\cap A'_1\neq\emptyset$ for $k=2$ is checked in Lean in the sanity file. The statement therefore excludes the last block as well as the last $A'_i$; the rest of the proof of Theorem 6.3 has room to discard one more block.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:27, Lemma 6.5 and the definition of B∗_j before it (context p. 3:26)

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_LexDFS

namespace TwinWidthI.MinorFree

/-- Lemma 6.5, p. 3:27, corrected. Context of Lemma 6.4 (a DFS, vertices `a i j` with neighbours
`b i j`, the `a i j` increasing in `i` and preceding every `b i' j'`), together with the blocks
`B j ∋ b i j`: each `B j` is consecutive in the discovery order, `B j` entirely precedes `B j'`
for `j < j'`, and every vertex of every `B j` is discovered after every `a i j`. Let
`A'_i = MinSubtree par {a i j | j}` and `B*_j = MinSubtree par (B j)`. Then `B*_j ∩ A'_i = ∅`
for every `i` and every `j` except the last ones (`i, j < k - 1`).

The page states it for every `j ∈ [g(t)/2]`; for the last block `B_{g(t)/2}` it can fail (its
vertices after `b_{g(t)/2, g(t)/2}` need not be in the subtree `𝒯[u]` the proof uses), so the
last block is excluded, like the last `A'_i`. -/
theorem lemma_6_5 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) {k : ℕ}
    (a b : Fin k → Fin k → V) (B : Fin k → Set V)
    (hab : ∀ i j, G.Adj (a i j) (b i j))
    (ha : ∀ i j i' j', i < i' → σ (a i j) < σ (a i' j'))
    (hbB : ∀ i j, b i j ∈ B j)
    (hBcons : ∀ j x y z, x ∈ B j → z ∈ B j → σ x ≤ σ y → σ y ≤ σ z → y ∈ B j)
    (hBord : ∀ j j' x y, j < j' → x ∈ B j → y ∈ B j' → σ x < σ y)
    (hAB : ∀ i j j' x, x ∈ B j' → σ (a i j) < σ x) :
    ∀ i j : Fin k, (i : ℕ) + 1 < k → (j : ℕ) + 1 < k →
      Disjoint (MinSubtree par (B j)) (MinSubtree par (Set.range (a i))) := by sorry

end TwinWidthI.MinorFree
