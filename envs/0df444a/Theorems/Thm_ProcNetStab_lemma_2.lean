-- Prove2me | Theorems.Thm_ProcNetStab_lemma_2
-- name    : ProcNetStab.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:45:47.366331+00:00
-- url     : https://prove2.me/theorems/8199a264-a095-4198-8eff-2e3ffb118ecc
-- title:
--   Lemma 2 (Sufficiency): $k$-WARPS $\Rightarrow$ rationalizable with $k$-anonymous preferences
-- statement:
--   Let $g$ be the observed network on the node set $V$, $L : V \to T$ a type map and $k \in \mathbb N$. If $g$ satisfies $k$-WARPS, then there exist preferences satisfying $k$-anonymity with respect to which $g$ is pairwise stable:
--   $$
--   g \text{ satisfies } k\text{-WARPS} \implies g \text{ rationalizable as pairwise stable with } k\text{-anonymous preferences}.
--   $$
--
--   This is the sufficiency half of Theorem 1: the axiom, a condition on the observed network alone, guarantees the existence of rationalizing preferences.
--
--   Differences from the source:
--
--   - generalization: node set N = {1,...,n} and a finite set T of types → arbitrary node type V, arbitrary type space T and type map L : V → T; reason: the finite case is an instance; T = Unit is the untyped Definition 3.4
--   - reading: g − ij, introduced only as removing a link (p.6), used for all agents in Definitions 3.1 and 3.9 → edge deletion h.deleteEdges {s(i,j)}, a no-op when ij ∉ h, with j ranging over all nodes; reason: literal notation; under it the theorem holds for every k, while restricting Definition 3.9 to ij ∈ h makes Theorem 1 false at k = 0 (two nodes, g empty: rationalizable but not 0-WARPS)
--   - reading: k-WARPS: "for all pairs of nodes i and j in the network" → i and j arbitrary nodes, not required to be linked or distinct; reason: Definition A.4 and the proof of Lemma 1 use no link ij; restricting to linked or distinct pairs makes Theorem 1 false (n = 5, k = 1, g = {01, 03, 24}, i = j = 0, i′j′ = 12)
--   - reading: Definition 3.9 with networks g, g′ → g, g′ of Definition 3.9 are universally quantified networks h, h′; the observed g enters only through the adjacency clause of ≃k; reason: Definition 3.9 binds g, g′; the proof of Lemma 1 applies it with h′ = g + i′j′
--   - encoding: networks (N,E), k-neighborhoods, preference relations ⪰_i ⊂ G × G → SimpleGraph V, the k-ball via the extended distance edist and the induced subgraph, relations pref a x y read as x ⪰_a y; reason: Lean conventions; same instances
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Lemma 2, p.14; proof pp.OA-2–OA-7

import Mathlib
import Definitions.Def_ProcNetStab_Rationalizable
import Definitions.Def_ProcNetStab_KWARPS

namespace ProcNetStab

/-- **Lemma 2 (Sufficiency)** (Chiong, Qi, *Stability of Procurement Networks* (authors'
manuscript, 2025), Lemma 2, p.14; proof pp.OA-2–OA-7): when the observed network `g` satisfies
`k`-WARPS, there are preferences satisfying `k`-anonymity with respect to which `g` is pairwise
stable. -/
theorem lemma_2 {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ) (hW : KWARPS L g k) :
    Rationalizable L g k := by sorry

end ProcNetStab
