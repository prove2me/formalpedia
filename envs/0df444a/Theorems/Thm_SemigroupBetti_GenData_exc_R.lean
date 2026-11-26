-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exc_R
-- name    : SemigroupBetti.GenData.exc_R
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:04:54.956655+00:00
-- url     : https://prove2.me/theorems/730e1403-fc4c-5b0d-ac11-8d5134f414f2
-- title:
--   Gen Data: exc R
-- statement:
--   The Gen Data construction uses the exc R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L101-L102
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L101-L102

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
variable {G}
variable (hA : G.A = 1) (hB : G.B = G.W - 1)
include hA hB
set_option linter.unusedSectionVars false

theorem SemigroupBetti.GenData.exc_R : G.R = G.W - 1 := by sorry
