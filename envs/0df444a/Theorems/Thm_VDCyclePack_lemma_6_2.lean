-- Prove2me | Theorems.Thm_VDCyclePack_lemma_6_2
-- name    : VDCyclePack.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:35.851193+00:00
-- url     : https://prove2.me/theorems/746cac07-9ad9-47e4-aeb1-168a5db9baf4
-- title:
--   Lemma 6.2 (cubic lemma, [EP65], [Die10, Lemma 2.3.1]): $q$ disjoint cycles in a cubic multigraph with at least $s_q$ vertices, found in polynomial time
-- statement:
--   Let $q\ge2$ and $s_q=4q(\log_2 q+\log_2\log_2 q+4)$. Then:
--
--   1. every cubic multigraph (loops and parallel edges allowed, a loop counting two in the degree) with at least $s_q$ vertices contains $q$ vertex-disjoint cycles;
--   2. such cycles can be found in polynomial time.
--
--   A loop is a cycle of length one and two parallel edges form a cycle of length two. In Proposition 6.3 the lemma is applied to the cubic multigraph obtained from many disjoint $A$-paths and the marked cycles by suppressing degree-two vertices.
--
--   **Formalization Note** A multigraph is a finite vertex type, a finite edge type and an end map to unordered pairs; cycles are given by vertex and edge sequences. In part 2 the multigraph is an edge list with positions as edge indices, and the algorithm outputs the $q$ cycles as index lists.
--
--   Differences from the source:
--   - encoding: a cubic multigraph with at least s_q vertices, q vertex-disjoint cycles → finite types W, E (any universe) with ends : E → Sym2 W and IsCubic (loops count 2), s_q ≤ Fintype.card W in ℝ; q cycles IsMCycle with pairwise disjoint vertex lists; reason: the paper's multigraph conventions (p.10); for q ≥ 2, log₂ log₂ q ≥ 0, so no junk value of the logarithm occurs
--   - reading: such cycles can be found in polynomial time → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime (encMInst ++ encWNat) encMCycles alg); on every encoded cubic multigraph with ≥ s_q vertices and q ≥ 2 the output is the index lists of q valid, pairwise vertex-disjoint cycles; reason: the standard Turing-machine reading: Mathlib's TM2 machines are deterministic, numbers are written in binary, and the machine must halt in polynomial time on every input while its output is constrained only on inputs meeting the hypotheses
--   - encoding: the multigraph given as input → an MInst: n and a list of vertex pairs in Fin n, edges indexed by list position (equal ends = loop, repeated pairs = parallel edges); reason: every finite multigraph has such a description; same instances
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 6.2, p.18

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_VDCyclePack_encWNat
import Definitions.Def_VDCyclePack_IsCubic
import Definitions.Def_VDCyclePack_IsMCycle
import Definitions.Def_VDCyclePack_MInst_ends
import Definitions.Def_VDCyclePack_encMInst
import Definitions.Def_VDCyclePack_encMCycles

universe u

namespace VDCyclePack

/-- **Lemma 6.2 (cubic multigraphs; [EP65], [Die10, Lemma 2.3.1]).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 6.2, p.18: "Let q ≥ 2 and s_q = 4q(log q + log log q + 4). Every cubic multigraph
with at least s_q vertices contains q vertex-disjoint cycles, and such cycles can be found in
polynomial time."

* **(A)** For every `q ≥ 2` and every finite cubic multigraph (loops and parallel edges allowed, a
  loop counting two in the degree) with at least `s_q = 4q(log₂ q + log₂ log₂ q + 4)` vertices,
  there are `q` cycles with pairwise disjoint vertex sets.
* **(B)** There is a map `alg`, computable by a Turing machine in time polynomial in the binary
  length of `(B, q)`, that on every encoded cubic multigraph `B` with at least `s_q` vertices and
  every `q ≥ 2` outputs `q` such cycles (vertex lists and edge-index lists).

**Formalization Note.** A multigraph is a finite vertex type, a finite edge type and an end map to
`Sym2`; cycles are `IsMCycle` (a loop is a cycle of length one, two parallel edges one of length
two). In (B) the multigraph is an `MInst` (edges indexed by list position) encoded by `encMInst`,
followed by the word of `q`; the output, encoded by `encMCycles`, is the list of the `q` cycles with
vertices and edges as indices. For `q = 2`, `log₂ log₂ 2 = 0`. -/
theorem lemma_6_2 :
    (∀ (W E : Type u) [Fintype W] [Fintype E] (ends : E → Sym2 W) (q : ℕ), 2 ≤ q →
      IsCubic ends → 4 * (q : ℝ) * (Real.logb 2 q + Real.logb 2 (Real.logb 2 q) + 4) ≤ (Fintype.card W : ℝ) →
      ∃ cyc : Fin q → List W × List E, (∀ i, IsMCycle ends (cyc i).1 (cyc i).2) ∧
        ∀ i j, i ≠ j → List.Disjoint (cyc i).1 (cyc j).1) ∧
    ∃ alg : MInst × ℕ → List (List ℕ × List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime (fun p : MInst × ℕ => encMInst p.1 ++ encWNat p.2)
        encMCycles alg) ∧
      ∀ (B : MInst) (q : ℕ), 2 ≤ q → IsCubic B.ends → 4 * (q : ℝ) * (Real.logb 2 q + Real.logb 2 (Real.logb 2 q) + 4) ≤ (B.n : ℝ) →
        ∃ cyc : Fin q → List (Fin B.n) × List (Fin B.edges.length),
          (∀ i, IsMCycle B.ends (cyc i).1 (cyc i).2) ∧
          (∀ i j, i ≠ j → List.Disjoint (cyc i).1 (cyc j).1) ∧
          alg (B, q) = List.ofFn fun i => ((cyc i).1.map Fin.val, (cyc i).2.map Fin.val) := by sorry

end VDCyclePack
