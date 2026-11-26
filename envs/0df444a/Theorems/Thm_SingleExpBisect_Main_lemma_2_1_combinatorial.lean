-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_2_1_combinatorial
-- name    : SingleExpBisect.Main.lemma_2_1_combinatorial
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:10:12.616063+00:00
-- url     : https://prove2.me/theorems/13805061-6238-4882-96ab-b3ac4d10dab2
-- title:
--   Lemma 2.1 (combinatorial clauses) — every connected cut has an important extension, and at most 4^ℓ important cuts have size ≤ ℓ
-- statement:
--   Let S and T be disjoint sets of vertices in a finite undirected graph, with S nonempty and inducing a connected graph. Every connected S–T cut C is contained in an important connected cut of no greater boundary size. For every nonnegative budget ℓ, there are at most 4^ℓ important connected S–T cuts of boundary size at most ℓ. These are the two combinatorial claims of Lemma 2.1. The enumeration-machine claim is stated in its parent lemma.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §2, p. 13, Lemma 2.1 (cited from [CFK+15, Theorems 8.11 and 8.13]) and the sentence before it

import Mathlib
import Definitions.Def_SingleExpBisect_Main_Graphs
open scoped Classical

namespace SingleExpBisect.Main
open MinBisectFPT
theorem lemma_2_1_combinatorial :
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (S T : Finset (Fin n)),
      Disjoint S T → (H.induce (S : Set (Fin n))).Connected →
      (∀ C : Finset (Fin n), IsConnCut H S T C →
          ∃ D : Finset (Fin n), IsImportantConnCut H S T D ∧ C ⊆ D ∧ cutSize H D ≤ cutSize H C) ∧
        ∀ ℓ : ℕ, ((Finset.univ : Finset (Finset (Fin n))).filter
          (fun D => IsImportantConnCut H S T D ∧ cutSize H D ≤ ℓ)).card ≤ 4 ^ ℓ := by sorry
end SingleExpBisect.Main
