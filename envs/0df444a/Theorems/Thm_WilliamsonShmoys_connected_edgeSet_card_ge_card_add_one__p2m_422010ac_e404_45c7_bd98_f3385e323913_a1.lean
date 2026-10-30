-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edgeSet_card_ge_card_add_one__p2m_422010ac_e404_45c7_bd98_f3385e323913_a1
-- name    : WilliamsonShmoys.connected_edgeSet_card_ge_card_add_one__p2m_422010ac_e404_45c7_bd98_f3385e323913_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:39:34.643261+00:00
-- url     : https://prove2.me/theorems/3b1e17ee-538b-4c52-b699-0702314938ce
-- title:
--   A finite connected graph has at least one fewer edge than vertices
-- statement:
--   Every finite connected simple graph has at least `|V| - 1` edges, expressed without natural subtraction as `|V| ≤ |E| + 1`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_edgeSet_card_ge_card_add_one__p2m_422010ac_e404_45c7_bd98_f3385e323913_a1 {V : Type} [Fintype V] (H : SimpleGraph V) : H.Connected → Fintype.card V ≤ H.edgeSet.ncard + 1 := by sorry
