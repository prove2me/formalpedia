-- Prove2me | Theorems.Thm_VDCyclePack_lemma_4_1
-- name    : VDCyclePack.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:12:07.774031+00:00
-- url     : https://prove2.me/theorems/a72eed2d-6a81-4580-9886-aafd9ba1dba2
-- title:
--   Lemma 4.1 (Solving the natural LP): an optimal fractional packing, as an explicit list of cycles with positive rational weights, in polynomial time
-- statement:
--   Let $G$ be a finite simple graph. One can compute in polynomial time an **optimal fractional packing** of $G$, that is, a feasible solution $x$ of the natural LP (1) with
--   $$
--   \sum_{C\in\mathcal C(G)}x_C=\nu^*(G),
--   $$
--   given as an explicit list of polynomially many cycles $C_1,\dots,C_m$ of $G$ with positive rational weights $x_{C_1},\dots,x_{C_m}$ (all other cycles have weight $0$).
--
--   This is the first step of the algorithm of Theorem 1.1; the LP has one variable per cycle, possibly exponentially many, and is solved through its dual.
--
--   **Formalization Note** The algorithm is a map from encoded graphs to lists of (vertex list, rational) entries, computed by a Mathlib `TM2` machine in time polynomial in the binary length of the input; its output length, hence the number of cycles, is polynomial automatically. No two entries describe the same cycle.
--
--   Differences from the source:
--   - reading: one can compute in polynomial time → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime encGraph encWeighted alg), correct on every encoded graph; reason: the standard Turing-machine reading: Mathlib's TM2 machines are deterministic, numbers are written in binary, and the machine must halt in polynomial time on every input while its output is constrained only on inputs meeting the hypotheses
--   - encoding: a finite simple undirected graph G given as input → a GraphInst (n and a list of index pairs) read through GraphInst.toGraph on Fin n; loops, repeats, both orientations and out-of-range pairs are ignored, so no well-formedness hypothesis; reason: every finite simple graph is isomorphic to such a graph and the statement is invariant under relabelling; same instances
--   - encoding: an explicit list of polynomially many cycles with positive rational weights → a List (List ℕ × ℚ): every entry IsCycleList with weight > 0, no two entries representing the same cycle; the weighting is listWeight (0 off the list); polynomially many follows from the polynomial running time; reason: a cycle given by its cyclic vertex sequence; same instances
--   - encoding: optimal fractional packing → IsFracPacking (toGraph I) (listWeight I (alg I)) and value = nuStar (toGraph I); reason: nuStar is the LP optimum (a supremum attained on a nonempty bounded set)
--   - generalization: polynomial in the size of the input graph, n = |V(G)| vertices included → polynomial in the length of the word, where n is one binary number, so isolated vertices add no length; reason: isolated vertices lie on no cycle or A-path, so a machine can ignore them and mention only indices of the edge list; a bound in the shorter word is in particular polynomial in the paper's size
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 4.1, p.11

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_VDCyclePack_GraphInst_toGraph
import Definitions.Def_VDCyclePack_IsCycleList
import Definitions.Def_VDCyclePack_Represents
import Definitions.Def_VDCyclePack_listWeight
import Definitions.Def_VDCyclePack_IsFracPacking
import Definitions.Def_VDCyclePack_value
import Definitions.Def_VDCyclePack_nuStar
import Definitions.Def_VDCyclePack_encGraph
import Definitions.Def_VDCyclePack_encWeighted

namespace VDCyclePack

/-- **Lemma 4.1 (solving the natural LP).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 4.1, p.11: "One can compute in polynomial time an optimal fractional packing
of G, given as an explicit list of polynomially many cycles with positive rational weights."

There is a map `alg` from encoded graphs to lists of (cycle, weight) entries, computable by a
Turing machine in time polynomial in the binary length of the input, such that for every graph
`I` every entry of `alg I` is a cycle of `I.toGraph` with a positive rational weight, the induced
weighting `listWeight I (alg I)` is a fractional packing, and its value is `ν*(I.toGraph)`.
Distinct entries describe distinct cycles, so the list is a list of cycles with their weights.

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with input encoding
`encGraph` and output encoding `encWeighted` (alphabet `OnlineCRS.Combine.Sym`, binary numbers);
the output length is then polynomial automatically. No cycle is listed twice (no two entries
represent the same subgraph). Optimality is equality with `nuStar`, the supremum of the LP (1). -/
theorem lemma_4_1 :
    ∃ alg : GraphInst → List (List ℕ × ℚ),
      Nonempty (Turing.TM2ComputableInPolyTime encGraph encWeighted alg) ∧
      ∀ I : GraphInst, (∀ e ∈ alg I, IsCycleList I e.1 ∧ 0 < e.2) ∧
        (alg I).Pairwise (fun e e' => ∀ C, Represents I e.1 C → ¬ Represents I e'.1 C) ∧
        IsFracPacking I.toGraph (listWeight I (alg I)) ∧
        value I.toGraph (listWeight I (alg I)) = nuStar I.toGraph := by sorry

end VDCyclePack
