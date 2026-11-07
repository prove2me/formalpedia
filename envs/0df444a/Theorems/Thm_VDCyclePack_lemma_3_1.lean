-- Prove2me | Theorems.Thm_VDCyclePack_lemma_3_1
-- name    : VDCyclePack.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:42.748936+00:00
-- url     : https://prove2.me/theorems/bd619734-c6d5-42dd-a9ae-6526d611bb2d
-- title:
--   Lemma 3.1 (Gallai): $M$ disjoint $A$-paths or $2M-2$ vertices meeting every $A$-path; a maximum family in polynomial time
-- statement:
--   Let $F$ be a finite simple graph, let $A\subseteq V(F)$, and let $M\ge1$ be an integer. Then:
--
--   1. $F$ contains $M$ vertex-disjoint $A$-paths, or some set of at most $2M-2$ vertices meets every $A$-path in $F$;
--   2. one can compute in polynomial time a maximum family of vertex-disjoint $A$-paths in $F$.
--
--   This consequence of Gallai's min–max formula is used, with $F=G-E(H)$ and $A=V(H)$, in Proposition 6.3.
--
--   **Formalization Note** In part 2 the graph is encoded and $A$ is the list of the indices of its vertices; the output is a list of vertex sequences of pairwise disjoint $A$-paths such that $F$ has no family of one more disjoint $A$-paths.
--
--   Differences from the source:
--   - encoding: a graph F (finite and simple, p.9), A ⊆ V(F), M ≥ 1 → F : SimpleGraph V with Fintype V (V in any universe), A : Set V, 1 ≤ M; A-paths IsAPath, M disjoint ones HasDisjointAPaths, X with X.card ≤ 2 * M - 2 and MeetsAllAPaths; reason: the paper's definitions (p.10); 2M − 2 is not truncated since M ≥ 1
--   - reading: one can compute in polynomial time a maximum family of vertex-disjoint A-paths in F → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime (encGraph ++ encWList encWNat) encCycles alg); the output lists are the vertex sequences of pairwise disjoint A-paths of toGraph, and ¬ HasDisjointAPaths for one more path; reason: the standard Turing-machine reading: Mathlib's TM2 machines are deterministic, numbers are written in binary, and the machine must halt in polynomial time on every input while its output is constrained only on inputs meeting the hypotheses
--   - encoding: a finite simple undirected graph G given as input → a GraphInst (n and a list of index pairs) read through GraphInst.toGraph on Fin n; loops, repeats, both orientations and out-of-range pairs are ignored, so no well-formedness hypothesis; reason: every finite simple graph is isomorphic to such a graph and the statement is invariant under relabelling; same instances
--   - encoding: a maximum family → pairwise disjoint A-paths, k of them, with ¬ HasDisjointAPaths F A (k + 1); reason: k + 1 disjoint A-paths exist whenever more than k do (take a subfamily), so this is maximum cardinality
--   - encoding: A ⊆ V(F) as part of the input → a list As of indices, A = {w | w.val ∈ As}; reason: same instances
--   - generalization: polynomial in the size of the input graph, n = |V(G)| vertices included → polynomial in the length of the word, where n is one binary number, so isolated vertices add no length; reason: isolated vertices lie on no cycle or A-path, so a machine can ignore them and mention only indices of the edge list; a bound in the shorter word is in particular polynomial in the paper's size
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 3.1, p.10

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_VDCyclePack_encWNat
import Definitions.Def_VDCyclePack_encWList
import Definitions.Def_VDCyclePack_IsAPath
import Definitions.Def_VDCyclePack_HasDisjointAPaths
import Definitions.Def_VDCyclePack_MeetsAllAPaths
import Definitions.Def_VDCyclePack_GraphInst_toGraph
import Definitions.Def_VDCyclePack_encGraph
import Definitions.Def_VDCyclePack_encCycles

universe u

namespace VDCyclePack

/-- **Lemma 3.1 (Gallai).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 3.1, p.10: "Let F be a graph, let A ⊆ V(F), and let M ≥ 1 be an integer. Then F
contains M vertex-disjoint A-paths, or some set of at most 2M − 2 vertices meets every A-path in F.
Moreover, one can compute in polynomial time a maximum family of vertex-disjoint A-paths in F."
(A consequence of Gallai's min-max formula [Gal61]; algorithmic part via [Edm65], [Sch03, Ch. 73].)

* **(A)** For every finite graph `F`, set `A` of vertices and integer `M ≥ 1`, either `F` has `M`
  vertex-disjoint A-paths, or some set `X` of at most `2M − 2` vertices meets every A-path of `F`.
* **(B)** There is a map `alg`, computable by a Turing machine in time polynomial in the binary
  length of `(F, A)`, returning a list of pairwise disjoint vertex lists, each the vertex sequence
  of an A-path of `F`, such that `F` has no family of one more vertex-disjoint A-paths (a maximum
  family).

**Formalization Note.** In (B) the graph is `I.toGraph` and `A` is the set of vertices whose index is
listed; input encoding `encGraph` followed by the length-prefixed list of indices, output
`encCycles`. Maximality is `¬ HasDisjointAPaths F A (k + 1)` for the output size `k`; having `k + 1`
disjoint A-paths implies having any fewer, so this is maximum cardinality. -/
theorem lemma_3_1 :
    (∀ (V : Type u) [Fintype V] (F : SimpleGraph V) (A : Set V) (M : ℕ), 1 ≤ M →
      HasDisjointAPaths F A M ∨ ∃ X : Finset V, X.card ≤ 2 * M - 2 ∧ MeetsAllAPaths F A X) ∧
    ∃ alg : GraphInst × List ℕ → List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime
        (fun p : GraphInst × List ℕ => encGraph p.1 ++ encWList encWNat p.2) encCycles alg) ∧
      ∀ (I : GraphInst) (As : List ℕ),
        (∀ l ∈ alg (I, As), ∃ (u v : Fin I.n) (p : I.toGraph.Walk u v),
          IsAPath I.toGraph {w | w.val ∈ As} p ∧ p.support.map Fin.val = l) ∧
        (alg (I, As)).Pairwise List.Disjoint ∧
        ¬ HasDisjointAPaths I.toGraph {w | w.val ∈ As} ((alg (I, As)).length + 1) := by sorry

end VDCyclePack
