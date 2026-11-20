-- Prove2me | Theorems.Thm_VWZClique_free_words
-- name    : VWZClique.free_words
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T01:01:43.720769+00:00
-- url     : https://prove2.me/theorems/4be70549-b5ab-443f-a731-0242877517ab
-- title:
--   Lemma 3.2 — Free-coordinate bijection
-- statement:
--   The support of a partial swap is in bijection with pairs of free-coordinate strings. Under this bijection the two wedge-edge weights depend on the same free string and center. The statement is the local bijection used in the proof.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Lemma 3.2, proof. https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_Free

open VWZClique

theorem VWZClique.free_words {L : ℕ} (m : Mask L) (x y : PairBits L) :
    swapOK m x y ↔ ∃! pq : Free m × Free m, expand m pq = (x,y) := by sorry
