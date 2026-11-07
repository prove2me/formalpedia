-- Prove2me | Theorems.Thm_VDCyclePack_theorem_4_2_polytime
-- name    : VDCyclePack.theorem_4_2_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:12:04.395222+00:00
-- url     : https://prove2.me/theorems/37c4e632-a83e-4959-be18-57ad19863802
-- title:
--   Theorem 4.2 (Rounding), polynomial-time part: the packing $P$ is found in polynomial time (existence: theorem_4_2)
-- statement:
--   There is a polynomial-time algorithm that, given a finite simple graph $G$ and an explicit list of cycles $S$ of $G$ with positive rational weights $(x_C)_{C\in S}$ whose loads are at most one at every vertex, returns a family $P\subseteq S$ of pairwise vertex-disjoint cycles such that, for **every** pair $\alpha,\gamma\ge0$ for which every $R\subseteq S$ with $t=|R|$ satisfies $\beta(\bigcup_{C\in R}C)\le\alpha t+\gamma t\log_2(t+2)$,
--   $$
--   |P|\ \ge\ \Bigl\lceil\frac{T}{1+16\alpha+16\gamma\log_2(T+3)}\Bigr\rceil,\qquad T=\sum_{C\in S}x_C .
--   $$
--
--   This is the "one can find in polynomial time" clause of Theorem 4.2; the existence part is `VDCyclePack.theorem_4_2`. As on p.15, the parameters $\alpha,\gamma$ are used only in the analysis: the algorithm does not receive them.
--
--   **Formalization Note** A map on (encoded graph, list of (vertex list, rational) entries), computed by a Mathlib `TM2` machine in polynomial time, returning vertex lists. The family $S$ and the weights are decoded with the same predicates as in `theorem_4_2`.
--
--   Differences from the source:
--   - reading: one can find in polynomial time a family P ⊆ S → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime (encGraph ++ encWeighted) encCycles alg); for every admissible input and every α, γ ≥ 0 with StructBound the output satisfies the bound (the machine does not receive α, γ); reason: the standard Turing-machine reading: Mathlib's TM2 machines are deterministic, numbers are written in binary, and the machine must halt in polynomial time on every input while its output is constrained only on inputs meeting the hypotheses
--   - encoding: a finite simple undirected graph G given as input → a GraphInst (n and a list of index pairs) read through GraphInst.toGraph on Fin n; loops, repeats, both orientations and out-of-range pairs are ignored, so no well-formedness hypothesis; reason: every finite simple graph is isomorphic to such a graph and the statement is invariant under relabelling; same instances
--   - generalization: an explicitly given family S of cycles (each cycle once) with positive rational weights → a list ws of (vertex list, rational) entries, each IsCycleList with weight > 0, possibly listing a cycle more than once; S = familyOf I (ws.map Prod.fst), weights listWeight I ws (repeated weights add up), WeightedFamily S x; reason: a list without repetitions is the paper's input; with repetitions the hypotheses are those of the merged family
--   - encoding: a family P ⊆ S of pairwise vertex-disjoint cycles, |P| → a list of vertex lists, each representing a member of S, pairwise disjoint as lists; |P| is the list length; reason: disjoint nonempty vertex lists describe distinct, vertex-disjoint cycles; same instances
--   - encoding: β(⋃_{C∈R} C), log → cycleRank (R.sup id), the minimum size of a feedback edge set of the union in the subgraph lattice; Real.logb 2; reason: the paper's definition of β (p.10), of unions (p.9) and of logarithms (base two, p.9)
--   - generalization: polynomial in the size of the input graph, n = |V(G)| vertices included → polynomial in the length of the word, where n is one binary number, so isolated vertices add no length; reason: isolated vertices lie on no cycle or A-path, so a machine can ignore them and mention only indices of the edge list; a bound in the shorter word is in particular polynomial in the paper's size
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 4.2, p.12; Section 5, p.15

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_VDCyclePack_GraphInst_toGraph
import Definitions.Def_VDCyclePack_IsCycleList
import Definitions.Def_VDCyclePack_Represents
import Definitions.Def_VDCyclePack_listWeight
import Definitions.Def_VDCyclePack_familyOf
import Definitions.Def_VDCyclePack_WeightedFamily
import Definitions.Def_VDCyclePack_StructBound
import Definitions.Def_VDCyclePack_TR
import Definitions.Def_VDCyclePack_roundingDenom
import Definitions.Def_VDCyclePack_encGraph
import Definitions.Def_VDCyclePack_encWeighted
import Definitions.Def_VDCyclePack_encCycles

namespace VDCyclePack

/-- **Theorem 4.2 (rounding), polynomial time.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 4.2, p.12: "Then one can find in polynomial time a family P ⊆ S of pairwise
vertex-disjoint cycles with |P| ≥ ⌈T / (1 + 16α + 16γ log(T + 3))⌉." (hypotheses as in
`theorem_4_2`); p.15: "The parameters α and γ are used only in the analysis."

There is a map `alg`, computable by a Turing machine in time polynomial in the binary length of
its input, that takes an encoded graph `I` and an explicit list `ws` of (cycle, positive rational
weight) entries and returns a list of vertex lists, such that: whenever the entries are cycles of
`I.toGraph` with positive weights whose family `S` has loads at most one, then for **every**
`α, γ ≥ 0` satisfying the structural bound for `S`, every output list represents a member of `S`,
the output lists are pairwise disjoint (vertex-disjoint cycles), and there are at least
`⌈T / (1 + 16α + 16γ log₂(T + 3))⌉` of them, `T` the total weight.

**Formalization Note.** Input encoding `encGraph` followed by `encWeighted`, output encoding
`encCycles`, alphabet `OnlineCRS.Combine.Sym`. The machine does not receive `α, γ`: one machine
serves every admissible pair. The family `S` is `familyOf I (ws.map Prod.fst)` and the weights are
`listWeight I ws` (a cycle listed twice gets the sum of its weights), read with the same
`WeightedFamily`, `StructBound`, `TR` and `roundingDenom` as `theorem_4_2`. The machine halts in
polynomial time on every input; its output is constrained only on inputs meeting the
hypotheses. -/
theorem theorem_4_2_polytime :
    ∃ alg : GraphInst × List (List ℕ × ℚ) → List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime
        (fun p : GraphInst × List (List ℕ × ℚ) => encGraph p.1 ++ encWeighted p.2) encCycles alg) ∧
      ∀ (I : GraphInst) (ws : List (List ℕ × ℚ)),
        (∀ e ∈ ws, IsCycleList I e.1 ∧ 0 < e.2) →
        WeightedFamily (familyOf I (ws.map Prod.fst)) (listWeight I ws) →
        ∀ α γ : ℝ, 0 ≤ α → 0 ≤ γ → StructBound (familyOf I (ws.map Prod.fst)) α γ →
          (∀ l ∈ alg (I, ws), ∃ C ∈ familyOf I (ws.map Prod.fst), Represents I l C) ∧
          (alg (I, ws)).Pairwise List.Disjoint ∧
          ⌈TR (familyOf I (ws.map Prod.fst)) (listWeight I ws) /
              roundingDenom α γ (TR (familyOf I (ws.map Prod.fst)) (listWeight I ws))⌉₊ ≤
            (alg (I, ws)).length := by sorry

end VDCyclePack
