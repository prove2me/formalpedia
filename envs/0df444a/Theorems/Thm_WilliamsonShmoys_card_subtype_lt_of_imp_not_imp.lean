-- Prove2me | Theorems.Thm_WilliamsonShmoys_card_subtype_lt_of_imp_not_imp
-- name    : WilliamsonShmoys.card_subtype_lt_of_imp_not_imp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:39:11.846813+00:00
-- url     : https://prove2.me/theorems/167333e6-5e94-4718-ba99-0b1460d0b151
-- title:
--   Strict growth of finite subtype cardinality
-- statement:
--   For predicates on a finite type, inclusion of their subtypes together with a witness belonging only to q makes the q-subtype strictly larger. In the parent proof, p is adjacency in K and q is adjacency in L; the additional adjacency supplies the strictness witness. Prove it by the subtype inclusion and the finite-cardinality theorem for an injective, non-surjective map.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.card_subtype_lt_of_imp_not_imp
    {α : Type} [Fintype α] (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x → q x)
    (hstrict : ∃ x, q x ∧ ¬ p x) :
    Fintype.card {x // p x} < Fintype.card {x // q x} := by sorry
