-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_supp_subset_compSupp
-- name    : SemigroupBetti.GenData.supp_subset_compSupp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:57.135366+00:00
-- url     : https://prove2.me/theorems/99ae51da-d82e-4324-965b-595bd07060a1
-- title:
--   Gen Data: supp subset comp Supp
-- statement:
--   The Gen Data construction uses the supp subset comp Supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L84-L86
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L84-L86

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

theorem SemigroupBetti.GenData.supp_subset_compSupp {d : ℕ} (z : G.fiber d) :
    supp z.1 ⊆ G.compSupp ((G.nabla d).connectedComponentMk z) := by sorry
