-- Prove2me | Theorems.Thm_WilliamsonShmoys_card_subtype_le_univ
-- name    : WilliamsonShmoys.card_subtype_le_univ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:44:52.063521+00:00
-- url     : https://prove2.me/theorems/5795427a-a1bb-455b-94d8-5f2a0bce3e83
-- title:
--   Subtype cardinality is bounded by the ambient finite type
-- statement:
--   A predicate subtype of a finite type has cardinality at most that of the ambient type, including when the predicate is empty. Apply the inclusion embedding from the subtype into α and the finite-cardinality bound for injections.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.card_subtype_le_univ
    {α : Type} [Fintype α] (p : α → Prop)
    [DecidablePred p] :
    Fintype.card {x // p x} ≤ Fintype.card α := by sorry
