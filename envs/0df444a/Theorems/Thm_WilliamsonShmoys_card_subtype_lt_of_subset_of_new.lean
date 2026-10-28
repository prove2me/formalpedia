-- Prove2me | Theorems.Thm_WilliamsonShmoys_card_subtype_lt_of_subset_of_new
-- name    : WilliamsonShmoys.card_subtype_lt_of_subset_of_new
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:28:57.3748+00:00
-- url     : https://prove2.me/theorems/768546c8-be25-4333-830b-91f4a1a14173
-- title:
--   A new point strictly increases finite subtype cardinality
-- statement:
--   For predicates on a finite type, if every P-point is a Q-point and there is a Q-point that is not a P-point, then the subtype satisfying Q has strictly larger cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.card_subtype_lt_of_subset_of_new
    {α : Type} [Fintype α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hsubset : ∀ x : α, P x → Q x)
    (a : α) (haQ : Q a) (haP : ¬ P a) :
    Fintype.card {x : α // P x} < Fintype.card {x : α // Q x} := by sorry
