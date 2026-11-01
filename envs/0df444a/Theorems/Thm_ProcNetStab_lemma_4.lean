-- Prove2me | Theorems.Thm_ProcNetStab_lemma_4
-- name    : ProcNetStab.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:41.044495+00:00
-- url     : https://prove2.me/theorems/81d89480-404b-40c1-ac66-282853cb7fda
-- title:
--   Lemma 4: $k$-WARPS gives a revealed preference profile with an acyclic extension
-- statement:
--   Let $g$ be the observed network on the node set $V$, $L : V \to T$ a type map and $k \in \mathbb N$. If $g$ satisfies $k$-WARPS, then there is a profile of revealed preference relations $\langle R, P\rangle \in \mathcal R(g)$ whose extension according to $\simeq_k$ (ExtendRevealed, Algorithm 1) is acyclic:
--   $$
--   g \text{ satisfies } k\text{-WARPS} \implies \exists\, \langle R, P\rangle \in \mathcal R(g):\ \mathrm{ExtendRevealed}(\langle R, P\rangle) \text{ is acyclic}.
--   $$
--
--   Together with Lemma 3 it gives the sufficiency half of Theorem 1.
--
--   Differences from the source:
--
--   - generalization: node set N = {1,...,n} and a finite set T of types → arbitrary node type V, arbitrary type space T and type map L : V → T; reason: the finite case is an instance; T = Unit is the untyped Definition 3.4
--   - reading: g − ij, introduced only as removing a link (p.6), used for all agents in Definitions 3.1 and 3.9 → edge deletion h.deleteEdges {s(i,j)}, a no-op when ij ∉ h, with j ranging over all nodes; reason: literal notation; under it the theorem holds for every k, while restricting Definition 3.9 to ij ∈ h makes Theorem 1 false at k = 0 (two nodes, g empty: rationalizable but not 0-WARPS)
--   - reading: k-WARPS: "for all pairs of nodes i and j in the network" → i and j arbitrary nodes, not required to be linked or distinct; reason: Definition A.4 and the proof of Lemma 1 use no link ij; restricting to linked or distinct pairs makes Theorem 1 false (n = 5, k = 1, g = {01, 03, 24}, i = j = 0, i′j′ = 12)
--   - reading: Definition 3.9 with networks g, g′ → g, g′ of Definition 3.9 are universally quantified networks h, h′; the observed g enters only through the adjacency clause of ≃k; reason: Definition 3.9 binds g, g′; the proof of Lemma 1 applies it with h′ = g + i′j′
--   - reading: R(g): profiles ⟨R,P⟩ that are "the smallest profile" satisfying clause 2 of Definition A.5, a disjunction → profiles parametrized by a valid choice C of revealing endpoints (a nonempty subset of {a, b} for each non-link ab); reason: a disjunctive clause has no unique smallest profile; Algorithm 2 and Definition A.8 put both endpoints in, so subsets (not single endpoints) are needed
--   - reading: ExtendRevealed (Algorithm 1), a single foreach pass in unspecified order with an if/else → the least profile containing ⟨R,P⟩ and closed under both propagation rules, with P* ⊆ R*; reason: the text describes iteration to a fixpoint ("At each iteration, we add at least one ordered pair"); the else only suppresses a pair that would close a cycle of length two, so acyclicity does not depend on it
--   - encoding: networks (N,E), k-neighborhoods, preference relations ⪰_i ⊂ G × G → SimpleGraph V, the k-ball via the extended distance edist and the induced subgraph, relations pref a x y read as x ⪰_a y; reason: Lean conventions; same instances
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Lemma 4, p.OA-5 (PDF p.34); proof pp.OA-5–OA-7

import Mathlib
import Definitions.Def_ProcNetStab_KWARPS
import Definitions.Def_ProcNetStab_ExtendRevealed
import Definitions.Def_ProcNetStab_IsAcyclic

namespace ProcNetStab

/-- **Lemma 4** (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript, 2025),
Lemma 4, p.OA-5 (PDF p.34); proof pp.OA-5–OA-7): when `k`-WARPS is satisfied, there is a profile
of revealed preference relations whose extension according to `≃k` (ExtendRevealed, Algorithm 1)
is acyclic. -/
theorem lemma_4 {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ) (hW : KWARPS L g k) :
    ∃ C : V → V → Prop, ValidChoice g C ∧
      ∀ a : V, IsAcyclic (ExtendRevealed L g k C true a) (ExtendRevealed L g k C false a) := by sorry

end ProcNetStab
