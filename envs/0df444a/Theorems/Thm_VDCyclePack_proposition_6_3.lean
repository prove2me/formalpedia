-- Prove2me | Theorems.Thm_VDCyclePack_proposition_6_3
-- name    : VDCyclePack.proposition_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:52.857379+00:00
-- url     : https://prove2.me/theorems/2222e245-99e4-4f6b-83e4-a403d2c6dd1c
-- title:
--   Proposition 6.3: $q$ disjoint cycles, or a certificate that there are no $M$ disjoint $A$-paths, in polynomial time
-- statement:
--   Let $q\ge2$, $M=8q\lceil\log_2(q+2)\rceil$, and let $H$ be a marked packing of a finite graph $G$, with $A=V(H)$ and $A$-paths taken in $G-E(H)$. Then:
--
--   1. if there are $M$ vertex-disjoint $A$-paths, then $G$ contains $q$ vertex-disjoint cycles; if there are not, some set of at most $2M-2$ vertices meets every $A$-path;
--   2. one can in polynomial time either find $q$ vertex-disjoint cycles in $G$ or certify that there are no $M$ vertex-disjoint $A$-paths.
--
--   In the proof of Lemma 4.3, the second outcome feeds the hitting set into Lemma 6.4.
--
--   **Formalization Note** In part 2 the marked packing is given by its cycles as pairwise disjoint vertex lists; the algorithm returns either $q$ disjoint cycles, or a "no" answer that is correct: $G-E(H)$ has no $M$ disjoint $A$-paths.
--
--   Differences from the source:
--   - encoding: a marked packing H, A = V(H), A-paths in G − E(H) → H = P.sup id for a cycle packing P (a Finset of pairwise vertex-disjoint cycle subgraphs); A = H.verts; A-paths are IsAPath in G.deleteEdges H.edgeSet; reason: the paper's definitions (pp.10–11); same instances
--   - reading: either find q vertex-disjoint cycles or certify that there are no M vertex-disjoint A-paths; in the latter case some set of at most 2M − 2 vertices meets every A-path → (A) HasDisjointAPaths M → ∃ cycle packing of size q, and ¬ HasDisjointAPaths M → ∃ X with X.card ≤ 2M − 2 meeting every A-path; (B) the machine returns some cs (q disjoint cycles) or none, and none only when ¬ HasDisjointAPaths M; reason: 'certify' read as a correct negative answer (the algorithm need not output X, p.19); the existence clauses are the combinatorial content of the dichotomy
--   - reading: one can in polynomial time either find q vertex-disjoint cycles in G or certify … → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime (encGraph ++ encCycles ++ encWNat) (Option encoding) alg), correct for q ≥ 2 and every list of pairwise disjoint cycle lists; reason: the standard Turing-machine reading: Mathlib's TM2 machines are deterministic, numbers are written in binary, and the machine must halt in polynomial time on every input while its output is constrained only on inputs meeting the hypotheses
--   - encoding: a finite simple undirected graph G given as input → a GraphInst (n and a list of index pairs) read through GraphInst.toGraph on Fin n; loops, repeats, both orientations and out-of-range pairs are ignored, so no well-formedness hypothesis; reason: every finite simple graph is isomorphic to such a graph and the statement is invariant under relabelling; same instances
--   - encoding: the marked packing H given as input; the q cycles output → pairwise disjoint IsCycleList vertex lists hs, H = (familyOf I hs).sup id; output cycles as pairwise disjoint IsCycleList lists; reason: same instances
--   - encoding: M = 8q⌈log(q + 2)⌉ → bigM q; reason: the paper's definition
--   - generalization: polynomial in the size of the input graph, n = |V(G)| vertices included, for an integer q → polynomial in the length of the word, where n is one binary number, so isolated vertices add no length, and q is a binary number; reason: isolated vertices lie on no cycle or A-path, so a machine can ignore them and mention only indices of the edge list; a bound in the shorter word is in particular polynomial in the paper's size; the proof compares M with the size of a family of disjoint A-paths, at most n/2, so a large q costs nothing
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Proposition 6.3, p.18 (q ≥ 2 and M from Section 6, p.17)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_VDCyclePack_encWNat
import Definitions.Def_VDCyclePack_IsCyclePacking
import Definitions.Def_VDCyclePack_HasDisjointAPaths
import Definitions.Def_VDCyclePack_MeetsAllAPaths
import Definitions.Def_VDCyclePack_bigM
import Definitions.Def_VDCyclePack_GraphInst_toGraph
import Definitions.Def_VDCyclePack_IsCycleList
import Definitions.Def_VDCyclePack_familyOf
import Definitions.Def_VDCyclePack_encGraph
import Definitions.Def_VDCyclePack_encCycles

universe u

namespace VDCyclePack

/-- **Proposition 6.3 (many A-paths give q disjoint cycles).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Proposition 6.3, p.18: "Given a marked packing H, one can in polynomial time either
find q vertex-disjoint cycles in G or certify that there are no M vertex-disjoint A-paths. In the
latter case, some set of at most 2M − 2 vertices meets every A-path." Here (Section 6, p.17) q ≥ 2
and M = 8q⌈log(q + 2)⌉, `A = V(H)`, and A-paths lie in `G − E(H)`.

* **(A)** For every cycle packing `P` of a finite graph `G`, `H = ⋃ P`, and `q ≥ 2`: if
  `G − E(H)` has `M` vertex-disjoint `V(H)`-paths then `G` has `q` vertex-disjoint cycles; if it has
  not, some set of at most `2M − 2` vertices meets every such path.
* **(B)** There is a map `alg`, computable by a Turing machine in time polynomial in the binary
  length of `(G, H, q)`, that on every graph, every list of pairwise vertex-disjoint cycles (the
  marked packing `H`) and every `q ≥ 2` returns either `some cs` with `cs` a list of `q` pairwise
  vertex-disjoint cycles of `G`, or `none`, and `none` only if `G − E(H)` has no `M` vertex-disjoint
  `V(H)`-paths.

**Formalization Note.** In (B) the marked packing is given by its cycles (vertex lists) and decoded
by `familyOf`; input encoding `encGraph`, `encCycles`, then the word of `q`; output `[0]` for `none`
(the certificate) and `1` followed by `encCycles` for `some`. -/
theorem proposition_6_3 :
    (∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (P : Finset G.Subgraph), IsCyclePacking P →
      ∀ q : ℕ, 2 ≤ q →
        (HasDisjointAPaths (G.deleteEdges (P.sup id).edgeSet) (P.sup id).verts (bigM q) →
          ∃ P' : Finset G.Subgraph, IsCyclePacking P' ∧ P'.card = q) ∧
        (¬ HasDisjointAPaths (G.deleteEdges (P.sup id).edgeSet) (P.sup id).verts (bigM q) →
          ∃ X : Finset V, X.card ≤ 2 * bigM q - 2 ∧
            MeetsAllAPaths (G.deleteEdges (P.sup id).edgeSet) (P.sup id).verts X)) ∧
    ∃ alg : GraphInst × List (List ℕ) × ℕ → Option (List (List ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime
        (fun p : GraphInst × List (List ℕ) × ℕ => encGraph p.1 ++ encCycles p.2.1 ++ encWNat p.2.2)
        (fun o : Option (List (List ℕ)) =>
          Option.elim o [(0 : OnlineCRS.Combine.Sym)] fun cs => (1 : OnlineCRS.Combine.Sym) :: encCycles cs)
        alg) ∧
      ∀ (I : GraphInst) (hs : List (List ℕ)) (q : ℕ), 2 ≤ q →
        (∀ l ∈ hs, IsCycleList I l) → hs.Pairwise List.Disjoint →
        Option.elim (alg (I, hs, q))
          (¬ HasDisjointAPaths (I.toGraph.deleteEdges ((familyOf I hs).sup id).edgeSet)
            ((familyOf I hs).sup id).verts (bigM q))
          fun cs => cs.length = q ∧ (∀ l ∈ cs, IsCycleList I l) ∧ cs.Pairwise List.Disjoint := by sorry

end VDCyclePack
