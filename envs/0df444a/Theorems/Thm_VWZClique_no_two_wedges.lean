-- Prove2me | Theorems.Thm_VWZClique_no_two_wedges
-- name    : VWZClique.no_two_wedges
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T01:01:08.710013+00:00
-- url     : https://prove2.me/theorems/2721534b-5a1d-481b-967e-a691de236ea2
-- title:
--   Lemma 3.1 — Patterns without two disjoint wedges
-- statement:
--   Every nine-position pattern without two vertex-disjoint wedges admits an arithmetic program of cost $O(n^5)$.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Lemma 3.1. https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_Weighted

open VWZClique

theorem VWZClique.no_two_wedges :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type*) [Field F] [CharZero F],
      ∀ (n : ℕ), 1 ≤ n → ∀ H : SimpleGraph V,
      (¬ ∃ f g : Fin 3 → V, wedge H f ∧ wedge H g ∧
        ∀ i j, f i ≠ g j) →
      computesWithin (weightedSum (F := F) (n := n) H) (C * (n : ℝ)^5) := by sorry
