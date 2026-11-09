-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_lemma_5_1
-- name    : ProportionalTSP.Exact.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:07.684882+00:00
-- url     : https://prove2.me/theorems/fd0934ca-444f-4c7f-802c-61d35b5c1795
-- title:
--   Lemma 5.1 — Simultaneous real realization of symbolic completion
-- statement:
--   For each fixed original graph with independent $R$ and costs $w$, there exists $\varepsilon>0$ such that
--   $$w^\varepsilon_e=x_0+\varepsilon x_1+\varepsilon^2x_2\quad\text{for }(x_0,x_1,x_2)=\widetilde w_e$$
--   has a generic cross-edge matrix and simultaneously preserves every feasible-load canonical assignment, every balanced-load coloring forest, and the entire set of minimum-cost tours of the completed graph. Realization is existential; no RAM instruction computes it. This connects the symbolic state construction with the real structural theorems without adding genericity to the headline input.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: Hamiltonian cycles counted as undirected cycles → finite unordered edge sets represented by a spanning simple cyclic list of length at least three; reason: rotations and reversal identify the same cycle, including in the parity count
--   - encoding: the unique minimum-cost assignment for generic costs → a finite argmin with least base-m assignment-rank tie rule, and a default only at infeasible loads; reason: the uniqueness clause is proved in Lemma 2.6; all theorem uses of canonical assignments have feasible loads
--   - encoding: distinct edge identifiers below n squared → the smaller vertex index times n plus the larger vertex index; reason: a deterministic injection on unordered nonloop edges satisfies precisely the identifier requirement
--   - encoding: real costs can reproduce the symbolic objects → the epsilon realization displayed in the proof on page 12, preserving the entire minimum-assignment relation even for empty parts and the coloring forests whenever their nonempty indexing is defined; reason: the proof supplies this concrete simultaneous realization; the algorithm still uses triples, not epsilon
--   - reading: The algorithm does not compute such a realization → not a conjunct of this item; the headline program receives no epsilon and has no real constant other than zero; reason: the sentence is a remark about the algorithm, not a property of the costs or of the realization, and it is enforced by the RAM syntax and the input encoding of Theorem 1.1
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Lemma 5.1, PDF p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem lemma_5_1 {m k : ℕ} (hkm : k ≤ m)
    (G : SimpleGraph (Vertex m k)) (hR : ∀ r s, ¬ G.Adj (.inr r) (.inr s))
    (w : Sym2 (Vertex m k) → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      let sw := symbolicCosts G w
      let rw := fun e => realize ε (sw e)
      Generic (cross rw) ∧
      (∀ (d : Load m) (A : Assignment m k),
        MinimumAssignment (cross rw) d A ↔
          (load A = d ∧ ∀ B : Assignment m k, load B = d →
            lexLE (assignmentCost (cross sw) A) (assignmentCost (cross sw) B))) ∧
      (∀ [NeZero m] [NeZero k], ∀ d : Load m, feasible k d → balanced d →
        coloringForest (cross rw) d = coloringForestBy (canonicalBy lexLE (cross sw)) d) ∧
      (∀ H : Finset (Sym2 (Vertex m k)),
        OptimalTour (completedGraph G) rw H ↔ SymbolicOptimal (completedGraph G) sw H) := by sorry

end ProportionalTSP.Exact
