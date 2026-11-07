-- Prove2me | Theorems.Thm_VDCyclePack_theorem_1_1
-- name    : VDCyclePack.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:12:08.059414+00:00
-- url     : https://prove2.me/theorems/a753985e-649c-40c9-9633-b3940cc73028
-- title:
--   Theorem 1.1: a deterministic polynomial-time algorithm returns at least $\nu^*(G)/(8192\lceil\sqrt{\lceil\log(\nu^*(G)+3)\rceil}\rceil)$ vertex-disjoint cycles
-- statement:
--   There is a deterministic polynomial-time algorithm that, given a finite simple undirected graph $G$, returns a family $P$ of pairwise vertex-disjoint cycles of $G$ with
--   $$
--   |P|\ \ge\ \frac{\nu^*(G)}{8192\,\Bigl\lceil\sqrt{\lceil\log_2(\nu^*(G)+3)\rceil}\Bigr\rceil},
--   $$
--   where $\nu^*(G)$ is the optimum of the natural LP relaxation (1) of vertex-disjoint cycle packing. In particular
--   $$
--   |P|=\Omega\Bigl(\frac{\nu^*(G)}{\sqrt{\log\nu^*(G)}}\Bigr)
--   $$
--   (with $\log x=\log_2\max\{2,x\}$ in asymptotic bounds, footnote 1), which is the statement of Theorem 1.1; the explicit bound is the one Section 4.4 proves.
--
--   Since $\nu(G)\le\nu^*(G)\le n/3$, the algorithm is an $O(\sqrt{\log n})$-approximation for Vertex-Disjoint Cycle Packing, and the integrality gap of the natural LP is $O(\sqrt{\log n})$.
--
--   **Formalization Note** The algorithm is a single map from encoded graphs (number of vertices and edge list, in binary) to lists of vertex lists, computed by a deterministic Mathlib `TM2` machine in time polynomial in the input length. Each output list is a cycle of the graph and the lists are pairwise disjoint.
--
--   Differences from the source:
--   - generalization: |P| = Ω(ν*(G)/√(log ν*(G))) (Theorem 1.1, p.3) → ν*(G) / (8192 · ⌈√⌈log₂(ν*(G) + 3)⌉⌉) ≤ |P| for every graph; reason: the explicit bound that Section 4.4 (p.13) says the proof establishes; since ⌈√⌈log₂(x + 3)⌉⌉ is at most a constant times √(log₂ max{2, x}) for x ≥ 0, it implies the Ω form under footnote 1's convention
--   - reading: there is a deterministic polynomial-time algorithm that, given G, returns P → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime encGraph encCycles alg), one machine for all graphs, correct on every encoded graph; reason: the standard Turing-machine reading: Mathlib's TM2 machines are deterministic, numbers are written in binary, and the machine must halt in polynomial time on every input while its output is constrained only on inputs meeting the hypotheses
--   - encoding: a finite simple undirected graph G given as input → a GraphInst (n and a list of index pairs) read through GraphInst.toGraph on Fin n; loops, repeats, both orientations and out-of-range pairs are ignored, so no well-formedness hypothesis; reason: every finite simple graph is isomorphic to such a graph and the statement is invariant under relabelling; same instances
--   - encoding: a family P of pairwise vertex-disjoint cycles, |P| → a list of vertex lists, each IsCycleList, pairwise disjoint as lists; |P| is the list length; reason: disjoint nonempty vertex lists of cycles describe distinct, vertex-disjoint cycles; same instances
--   - encoding: ν*(G), the optimum of the LP (1) over all cycles C ∈ C(G) → nuStar, the real supremum of the values of IsFracPacking weightings of cycles G (cycle subgraphs); reason: the set of values is nonempty and bounded, so the supremum is the LP optimum
--   - generalization: polynomial in the size of the input graph, n = |V(G)| vertices included → polynomial in the length of the word, where n is one binary number, so isolated vertices add no length; reason: isolated vertices lie on no cycle or A-path, so a machine can ignore them and mention only indices of the edge list; a bound in the shorter word is in particular polynomial in the paper's size
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 1.1, p.3, with the explicit bound of Section 4.4, p.13

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_VDCyclePack_GraphInst_toGraph
import Definitions.Def_VDCyclePack_IsCycleList
import Definitions.Def_VDCyclePack_nuStar
import Definitions.Def_VDCyclePack_encGraph
import Definitions.Def_VDCyclePack_encCycles

namespace VDCyclePack

/-- **Theorem 1.1: Ω(ν*/√log ν*) vertex-disjoint cycles in deterministic polynomial time.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 1.1, p.3: "There is a deterministic polynomial-time algorithm that, given a
finite simple undirected graph G, returns a family P of pairwise vertex-disjoint cycles with
|P| = Ω(ν*(G)/√(log ν*(G)))." Section 4.4, p.13: "More precisely, we show that the algorithm
returns a packing P satisfying the explicit bound |P| ≥ ν*(G) / (8192⌈√⌈log(ν*(G) + 3)⌉⌉)."

There is a map `alg` from encoded finite simple graphs to lists of vertex lists, computable by a
(deterministic) Turing machine in time polynomial in the binary length of the input, such that for
every graph `G = I.toGraph` the output is a family of cycles of `G` with pairwise disjoint vertex sets,
and the number of cycles is at least `ν*(G) / (8192·⌈√⌈log₂(ν*(G) + 3)⌉⌉)`, `ν*(G)` the optimum of
the natural LP (1).

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with input encoding
`encGraph` (binary numbers, edge list) and output encoding `encCycles`, over the alphabet
`OnlineCRS.Combine.Sym`; a TM2 machine is deterministic. One machine serves all graphs. The bound is
the explicit form of Section 4.4, which implies the `Ω` form of the theorem (with the paper's
convention `log x = log₂ max{2, x}` in asymptotic bounds, footnote 1). The bound is against the
fractional optimum `nuStar`. Vertices are `0, …, n − 1`. -/
theorem theorem_1_1 :
    ∃ alg : GraphInst → List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encGraph encCycles alg) ∧
      ∀ I : GraphInst, (∀ l ∈ alg I, IsCycleList I l) ∧ (alg I).Pairwise List.Disjoint ∧
        nuStar I.toGraph /
            (8192 * (⌈Real.sqrt (⌈Real.logb 2 (nuStar I.toGraph + 3)⌉₊ : ℝ)⌉₊ : ℝ)) ≤
          ((alg I).length : ℝ) := by sorry

end VDCyclePack
