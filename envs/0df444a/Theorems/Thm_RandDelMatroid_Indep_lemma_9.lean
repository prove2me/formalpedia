-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_9
-- name    : RandDelMatroid.Indep.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:30:13.126887+00:00
-- url     : https://prove2.me/theorems/e8071665-54d1-440e-8c5d-6b41c010854c
-- title:
--   Lemma 9 — completions exist
-- statement:
--   Let $T$ be a clean unordered decomposition tree of a regular matroid $M$, $u$ a node, and $Q$ a component of $T-u$ attached to $u$ through a 2- or 3-sum with boundary set $S$. Then for every $s\in S$ there is a completion of $s$ in $Q$: a set $P\subseteq E_Q\setminus S$ such that
--
--   $$P\cup\{s\} \text{ is a circuit of } M_Q.$$
--
--   Completions are what the absorption of Lemma 11 substitutes for boundary elements.
--
--   **Formalization Note** $Q$ is the component through the neighbour $v$ (`attachedComp T u v`), with $S=E_u\cap E_v\neq\emptyset$ (a 2- or 3-sum, since boundary sizes are 0, 1 or 3).
--
--   Differences from the source:
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
--   - reading: Definition 12.2: for every cographic, non-graphic node v with M_v = M*(G_v), every incident 3-element boundary S_e has a degree-3 vertex of G_v incident to all its edges → IsCleanDecompTree: some multigraph G_v with M_v* = M(G_v) has, for every incident tree edge with |S_e| = 3, a degree-3 vertex (loops counted twice) incident to all edges of S_e; reason: the condition is stated for the underlying graph of the node (§3.2, p. 15: 'a single vertex in the underlying graph'), a graph fixed once per node as in AF22's no-bad-nodes condition; the Lean reads G_v as that chosen graph (existential), not as every graph representing M_v
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 18, Lemma 9

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_DecompTree

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 9 (p. 18). Let `T` be a clean unordered decomposition tree of a regular matroid `M`, `u`
a node, and `Q` the component of `T - u` attached to `u` through the edge `{u, v}`, a 2- or 3-sum
with boundary set `S = S_{uv} ≠ ∅`. Then every `s ∈ S` has a completion in `Q`: a set
`P ⊆ E_Q \ S` such that `P ∪ {s}` is a circuit of `M_Q`. -/
theorem lemma_9 {β ι : Type} [Fintype ι] (M : Matroid β) (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsCleanDecompTree M T Mn) (u v : ι) (huv : T.Adj u v)
    (hS : (edgeBoundary Mn u v).Nonempty) (s : β) (hs : s ∈ edgeBoundary Mn u v) :
    ∃ P : Set β, IsCompletion T Mn (attachedComp T u v) (edgeBoundary Mn u v) s P := by sorry

end RandDelMatroid.Indep
