-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_8
-- name    : RandDelMatroid.Indep.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:30:14.080193+00:00
-- url     : https://prove2.me/theorems/9720ef7c-07de-47d0-b4cc-9c07781b1008
-- title:
--   Lemma 8 (corrected: M with at least one element) — every regular matroid has a clean unordered decomposition tree
-- statement:
--   Let $M$ be a regular matroid with at least one element. Then $M$ admits a clean unordered decomposition tree: a finite tree $T$ with nonempty regular node matroids $M_u$ satisfying Definitions 11 and 12, whose assembled matroid $M_T$ is isomorphic to $M$.
--
--   This is the structural input of the whole proof of Theorem 1 (§5.1 roots such a tree).
--
--   **Formalization Note** The node matroids contain fresh boundary elements that are not elements of $M$. The statement therefore relabels $M$ injectively into a type $\beta$ (`M.mapEmbedding φ`) and asks for a tree whose node matroids live on $\beta$ and whose assembled matroid equals the relabelled $M$; this is Definition 11.4's "$M_T$ is isomorphic to $M$".
--
--   Differences from the source:
--   - correction: every regular matroid M → every regular matroid M with M.E nonempty; reason: the empty matroid is regular but has no unordered decomposition tree: a tree has a node, node matroids are nonempty, and an element of a node ground set outside all boundary sets survives in E, while a node with only boundary elements violates the 1-/2-/3-sum size conditions (|E_u| ≥ 3, ≥ 7) or nonemptiness (p. 14 argument); so E ≠ ∅
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: matroid M = (E, I) with E a finite ground set (Definition 1) → Mathlib Matroid on an element type with finite ground set M.E; reason: Definition 1's matroids are finite; any finite matroid is a Lean Matroid with finite ground set
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
--   - reading: Definition 12.2: for every cographic, non-graphic node v with M_v = M*(G_v), every incident 3-element boundary S_e has a degree-3 vertex of G_v incident to all its edges → IsCleanDecompTree: some multigraph G_v with M_v* = M(G_v) has, for every incident tree edge with |S_e| = 3, a degree-3 vertex (loops counted twice) incident to all edges of S_e; reason: the condition is stated for the underlying graph of the node (§3.2, p. 15: 'a single vertex in the underlying graph'), a graph fixed once per node as in AF22's no-bad-nodes condition; the Lean reads G_v as that chosen graph (existential), not as every graph representing M_v
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 16, Lemma 8

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_DecompTree

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 8 (p. 16), for a regular matroid with at least one element. Every regular matroid `M`
(with `E ≠ ∅`) admits a clean unordered decomposition tree: after relabelling the elements of `M`
injectively into a type `β` that also holds the fresh boundary elements, there is a finite tree `T`
with node matroids `M_u` on `β` forming a clean unordered decomposition tree of (the relabelled) `M`. -/
theorem lemma_8 {α : Type} (M : Matroid α) [M.Finite] (hM : IsRegular M) (hne : M.E.Nonempty) :
    ∃ (β ι : Type) (_ : Fintype ι) (φ : α ↪ β) (T : SimpleGraph ι) (Mn : ι → Matroid β),
      IsCleanDecompTree (M.mapEmbedding φ) T Mn := by sorry

end RandDelMatroid.Indep
