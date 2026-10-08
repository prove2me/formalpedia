-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_lemma_6_6
-- name    : TwinWidthI.MinorFree.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:44.424935+00:00
-- url     : https://prove2.me/theorems/8c7b07a0-45af-46ee-9bdf-7696573b253a
-- title:
--   Lemma 6.6 — each component of 𝒯[v] − {v} meets at most two enhancements of the clique
-- statement:
--   Let $(v_1,\dots,v_n;\mathcal T)$ be a depth-first search of a finite graph $G$. Let $B_1,\dots,B_k$ be vertex sets, each consecutive in the discovery order, with $B_j$ entirely preceding $B_{j'}$ when $j<j'$, and let $B^*_j$ be the vertex set of the minimal subtree of $\mathcal T$ containing $B_j$. Let $J\subseteq[k]$ (the clique $C$ of the intersection graph of the $B^*_j$) and let $v$ be a vertex contained in every $B^*_j$, $j\in J$. If $c$ is a child of $v$ in $\mathcal T$, so that the subtree $\mathcal T[c]$ is a connected component of $\mathcal T[v]-\{v\}$, then
--
--   $$
--   \bigl|\{\,j\in J:\ B^*_j\cap\mathcal T[c]\neq\emptyset\,\}\bigr|\le 2 .
--   $$
--
--   In the proof of Theorem 6.3 this shows that the enhancements of the clique $C$ essentially intersect only at $v$, so the sets $D_j$ can be handled one component at a time.
--
--   **Formalization Note** The components $C_1,\dots,C_s$ of $\mathcal T[v]-\{v\}$ are the subtrees rooted at the children of $v$; a child is a vertex $c\neq v$ whose parent is $v$. The vertex $v$ is a hypothesis (the paper obtains it from the Helly property), as are the properties of the blocks that the proof uses.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:28, Lemma 6.6 and the sentence defining C_1, …, C_s before it

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_LexDFS

namespace TwinWidthI.MinorFree

open Classical in
/-- Lemma 6.6, p. 3:28. In a DFS (`σ`, `par`) of `G`, let `B j` (`j < k`) be blocks, each
consecutive in the discovery order, with `B j` entirely before `B j'` for `j < j'`, and let `J`
be a set of indices (the clique `C` of the intersection graph `H`) such that every
`B*_j = MinSubtree par (B j)`, `j ∈ J`, contains the vertex `v`. Let `c` be a child of `v`,
so that `𝒯[c] = {x | IsAncestor par c x}` is a connected component of `𝒯[v] − {v}`. Then at
most two of the `B*_j`, `j ∈ J`, intersect `𝒯[c]`. -/
theorem lemma_6_6 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) {k : ℕ}
    (B : Fin k → Set V)
    (hBcons : ∀ j x y z, x ∈ B j → z ∈ B j → σ x ≤ σ y → σ y ≤ σ z → y ∈ B j)
    (hBord : ∀ j j' x y, j < j' → x ∈ B j → y ∈ B j' → σ x < σ y)
    (J : Finset (Fin k)) (v : V) (hv : ∀ j ∈ J, v ∈ MinSubtree par (B j))
    (c : V) (hc : par c = v) (hcv : c ≠ v) :
    (J.filter fun j => ∃ x ∈ MinSubtree par (B j), IsAncestor par c x).card ≤ 2 := by sorry

end TwinWidthI.MinorFree
