-- Prove2me | Theorems.Thm_VDCyclePack_lemma_6_5
-- name    : VDCyclePack.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:50.528918+00:00
-- url     : https://prove2.me/theorems/be246dff-d60d-44f1-822d-2eabad6a0050
-- title:
--   Lemma 6.5 (edge Erdős–Pósa, [CJU20, Theorem 1]): no $r$ edge-disjoint cycles gives a feedback edge set of size at most $16r(\lceil\log 3r\rceil+1)$
-- statement:
--   Let $r\ge1$ be an integer. If a finite simple graph $F$ has no $r$ edge-disjoint cycles, then $F$ has a feedback edge set of size at most
--   $$
--   16r\bigl(\lceil\log_2(3r)\rceil+1\bigr),
--   $$
--   that is, a set of at most this many edges whose deletion leaves a forest.
--
--   This is the paper's specialization of the edge Erdős–Pósa theorem of Cames van Batenburg, Joret and Ulmer, used in Lemma 6.6 outside the marked vertices.
--
--   **Formalization Note** Cycles are cycle subgraphs; $r$ edge-disjoint cycles are $r$ cycle subgraphs with pairwise disjoint edge sets.
--
--   Differences from the source:
--   - encoding: a simple graph F (finite, p.9), r edge-disjoint cycles, a feedback edge set of size at most … → F : SimpleGraph W with Fintype W; ¬ ∃ r cycle subgraphs with pairwise disjoint edge sets; ∃ D ⊆ E(F) with (D.card : ℝ) ≤ 16 r (⌈log₂(3r)⌉₊ + 1) and F.deleteEdges D acyclic; reason: the paper's definitions (pp.9–10); log₂(3r) ≥ log₂ 3 > 0, so ⌈·⌉₊ is the ceiling
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 6.5, p.20

import Mathlib
import Definitions.Def_VDCyclePack_IsCycleSub

namespace VDCyclePack

/-- **Lemma 6.5 (edge Erdős–Pósa bound; [CJU20, Theorem 1]).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 6.5, p.20: "Let r ≥ 1 be an integer. If a simple graph F has no r edge-disjoint
cycles, then F has a feedback edge set of size at most 16r(⌈log(3r)⌉ + 1)."

Let `r ≥ 1` and let `F` be a finite simple graph that does not contain `r` cycles with pairwise
disjoint edge sets. Then some set `D` of at most `16r(⌈log₂(3r)⌉ + 1)` edges of `F` leaves a forest
when deleted.

**Formalization Note.** Cycles are subgraphs (`IsCycleSub`); `r` edge-disjoint cycles are `r`
cycle subgraphs with pairwise disjoint edge sets (hence distinct). A feedback edge set is a set of
edges of `F` whose deletion leaves an acyclic graph. Logarithms are base two. -/
theorem lemma_6_5 {W : Type*} [Fintype W] (F : SimpleGraph W) (r : ℕ) (hr : 1 ≤ r)
    (hF : ¬ ∃ Cs : Fin r → F.Subgraph, (∀ i, IsCycleSub (Cs i)) ∧
      ∀ i j, i ≠ j → Disjoint (Cs i).edgeSet (Cs j).edgeSet) :
    ∃ D : Finset (Sym2 W), (↑D : Set (Sym2 W)) ⊆ F.edgeSet ∧
      (D.card : ℝ) ≤ 16 * r * (⌈Real.logb 2 (3 * r)⌉₊ + 1) ∧
      (F.deleteEdges (↑D : Set (Sym2 W))).IsAcyclic := by sorry

end VDCyclePack
