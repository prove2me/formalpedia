-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_11_combinatorial
-- name    : SingleExpBisect.Main.lemma_3_11_combinatorial
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:18:27.005856+00:00
-- url     : https://prove2.me/theorems/88280d86-140d-40d6-8275-ca47a11afbf6
-- title:
--   Lemma 3.11 (family and size bound) — a downward-closed family covering bag traces of connected small cuts
-- statement:
--   For a finite graph G, mark a set B of vertices and fix a nonnegative cut budget k. There is a downward-closed family of subsets of B, each of size at most 2k, containing every trace A ∩ B of a connected set A with edge boundary at most k and trace size at most 2k, and containing the empty trace. The family contains at most 1 + |B| 2^(9k) sets. This is the combinatorial construction and size bound of Lemma 3.11. The machine-time guarantee is stated in the parent lemma.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.4, p. 27, Lemma 3.11

import Mathlib
import Definitions.Def_SingleExpBisect_Main_Graphs
open scoped Classical

namespace SingleExpBisect.Main
open MinBisectFPT
theorem lemma_3_11_combinatorial (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)) :
    ∃ L : Finset (Finset (Fin n)),
      (∀ D ∈ L, D ⊆ B ∧ D.card ≤ 2*k) ∧
      (∀ D ∈ L, ∀ D' : Finset (Fin n), D' ⊆ D → D' ∈ L) ∧
      L.card ≤ 1 + B.card * 2^(9*k) ∧
      ∀ A : Finset (Fin n), (A = ∅ ∨ (G.induce (A : Set (Fin n))).Connected) →
        cutSize G A ≤ k → (A ∩ B).card ≤ 2*k → A ∩ B ∈ L := by sorry
end SingleExpBisect.Main
