-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_5_1_combinatorial
-- name    : SingleExpBisect.Main.lemma_5_1_combinatorial
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:17:34.385867+00:00
-- url     : https://prove2.me/theorems/e94fb2b7-1d61-4292-aa7c-21fd68ffa34a
-- title:
--   Lemma 5.1 (structural alternative) — shrink a breakable bag preserving the distinguished set and adhesion
-- statement:
--   In a finite graph H let X be contained in a bag B, with at most 2k + 1 distinguished vertices and adhesion at most 2k. Either B is (2k,k)-edge-unbreakable or there exists a strictly smaller bag containing X and still having adhesion at most 2k. This is the conclusion about the output of Lemma 5.1, independent of machine runtime.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §5, p. 32, Lemma 5.1

import Mathlib
import Definitions.Def_SingleExpBisect_Main_Graphs
open scoped Classical

namespace SingleExpBisect.Main
open MinBisectFPT
theorem lemma_5_1_combinatorial {n : ℕ} (H : SimpleGraph (Fin n)) (k : ℕ) (X B : Finset (Fin n))
    (hXB : X ⊆ B) (hX : X.card ≤ 2*k+1) (hadh : adh H B ≤ 2*k) :
    IsEdgeUnbreakable H Finset.univ B (2*k) k ∨
      ∃ B' : Finset (Fin n), X ⊆ B' ∧ B'.card < B.card ∧ adh H B' ≤ 2*k := by sorry
end SingleExpBisect.Main
