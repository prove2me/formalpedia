-- Prove2me | Theorems.Thm_PCB_lex_positive_cone
-- name    : PCB.lex_positive_cone
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:16:20.372367+00:00
-- url     : https://prove2.me/theorems/e84644cf-0d97-4e21-856f-663ba92c290e
-- title:
--   The lexicographic cone is a positive cone (Theorem 4)
-- statement:
--   The lexicographic cone of Definition 2 is a positive cone in the sense of Definition 1: it is closed under products, it contains neither the identity nor the inverse of any of its elements, every non-identity element or its inverse lies in it, and it is invariant under conjugation. By the recipe of Definition 1, it defines a bi-invariant ordering on every almost-direct product of free groups. This is Theorem 4 of the paper, the main theorem of the mission.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Theorem 4, the main theorem).

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

namespace PCB

/-!  The goal (Theorem 4): the lexicographic cone of Definition 2 is a
positive cone: it is closed under products, it contains neither the
identity nor inverses of its elements, every non-identity element or its
inverse lies in it, and it is invariant under conjugation. It therefore
defines a bi-invariant ordering on every almost-direct product of free
groups. -/
theorem lex_positive_cone {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) :
    IsPositiveCone (lexCone W) := by sorry

end PCB
