-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_pos_of_two_le_ncomp
-- name    : SemigroupBetti.GenData.pos_of_two_le_ncomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:16.550171+00:00
-- url     : https://prove2.me/theorems/b9694c97-2866-5b2a-bd17-3afff14e77ff
-- title:
--   Gen Data: pos of two le ncomp
-- statement:
--   The Gen Data construction uses the pos of two le ncomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L128-L131
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L128-L131

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.pos_of_two_le_ncomp {d : ℕ} (h : 2 ≤ G.ncomp d) : 0 < d := by sorry
