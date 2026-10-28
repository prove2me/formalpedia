-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation_induced_edge_count_sum_card_sigma_edge_sets
-- name    : WilliamsonShmoys.component_edge_count_aggregation_induced_edge_count_sum.card_sigma_edge_sets
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:05:54.371968+00:00
-- url     : https://prove2.me/theorems/9735dda7-703b-4b24-ae80-f62a875ab3ed
-- title:
--   Cardinality of a finite dependent sum
-- statement:
--   The cardinality of a finite dependent sum equals the sum of the cardinalities of its fibers.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.component_edge_count_aggregation_induced_edge_count_sum.card_sigma_edge_sets
    {α β : Type} [Fintype β] (C : Finset β) (F : β → Type)
    [∀ b, Fintype (F b)] :
    Fintype.card (Σ b : C, F (b : β)) =
      C.sum (fun b => Fintype.card (F b)) := by sorry
