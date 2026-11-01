-- Prove2me | Theorems.Thm_ProcNetStab_theorem_1
-- name    : ProcNetStab.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:46:01.322604+00:00
-- url     : https://prove2.me/theorems/9be6285f-473b-4332-b122-89431ead2ff0
-- title:
--   Theorem 1: a network is rationalizable as pairwise stable with $k$-anonymous preferences iff it satisfies $k$-WARPS
-- statement:
--   Let $V$ be a set of agents, each with a type given by $L : V \to T$, let $g$ be the observed network on $V$, and let $k \in \mathbb N$. Then $g$ is rationalizable as pairwise stable with preferences that satisfy $k$-anonymity if and only if $g$ satisfies $k$-WARPS:
--   $$
--   \exists\, (\succeq_a)_{a \in V} \text{ weak orders on networks},\ k\text{-anonymous, with } g \text{ pairwise stable} \iff g \text{ satisfies } k\text{-WARPS}.
--   $$
--   Here $k$-WARPS says that for all agents $i, j$ there is no non-link $i'j' \notin g$ with $(i, g) \simeq_k (i', g + i'j')$ and $(j, g) \simeq_k (j', g + i'j')$, where $\simeq_k$ is rooted, type-preserving isomorphism of $k$-neighborhoods in networks adjacent to $g$.
--
--   This is the paper's main result: it characterizes the testable content of pairwise stability under the assumption that agents with the same local network position have the same incentives to form links, and it turns that content into a check on the observed network alone.
--
--   Differences from the source:
--
--   - generalization: node set N = {1,...,n} and a finite set T of types → arbitrary node type V, arbitrary type space T and type map L : V → T; reason: the finite case is an instance; T = Unit is the untyped Definition 3.4
--   - reading: g − ij, introduced only as removing a link (p.6), used for all agents in Definitions 3.1 and 3.9 → edge deletion h.deleteEdges {s(i,j)}, a no-op when ij ∉ h, with j ranging over all nodes; reason: literal notation; under it the theorem holds for every k, while restricting Definition 3.9 to ij ∈ h makes Theorem 1 false at k = 0 (two nodes, g empty: rationalizable but not 0-WARPS)
--   - reading: k-WARPS: "for all pairs of nodes i and j in the network" → i and j arbitrary nodes, not required to be linked or distinct; reason: Definition A.4 and the proof of Lemma 1 use no link ij; restricting to linked or distinct pairs makes Theorem 1 false (n = 5, k = 1, g = {01, 03, 24}, i = j = 0, i′j′ = 12)
--   - reading: Definition 3.9 with networks g, g′ → g, g′ of Definition 3.9 are universally quantified networks h, h′; the observed g enters only through the adjacency clause of ≃k; reason: Definition 3.9 binds g, g′; the proof of Lemma 1 applies it with h′ = g + i′j′
--   - encoding: networks (N,E), k-neighborhoods, preference relations ⪰_i ⊂ G × G → SimpleGraph V, the k-ball via the extended distance edist and the induced subgraph, relations pref a x y read as x ⪰_a y; reason: Lean conventions; same instances
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Theorem 1, p.15

import Mathlib
import Definitions.Def_ProcNetStab_Rationalizable
import Definitions.Def_ProcNetStab_KWARPS

namespace ProcNetStab

/-- **Theorem 1** (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript, 2025),
Theorem 1, p.15): an observed network `g` is rationalizable as pairwise stable with preferences
that satisfy `k`-anonymity if and only if `g` satisfies `k`-WARPS.

**Formalization Note** Stated for every `k ∈ ℕ` (including `k = 0`), every observed network `g`,
every node type `V`, type space `T` and type map `L` (`T = Unit` gives untyped networks). `g − ij`
is edge deletion, a no-op when `ij ∉ g`; the `k`-ball uses the extended distance `edist`;
preferences are relations on all networks on `V`. -/
theorem theorem_1 {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ) :
    Rationalizable L g k ↔ KWARPS L g k := by sorry

end ProcNetStab
