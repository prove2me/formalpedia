-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exc_p
-- name    : SemigroupBetti.GenData.exc_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:05:25.617814+00:00
-- url     : https://prove2.me/theorems/eaf6cc9e-dd81-4fa3-ad6c-510654514772
-- title:
--   Gen Data: exc p
-- statement:
--   The Gen Data construction uses the exc p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L104-L108
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L104-L108

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

theorem SemigroupBetti.GenData.exc_p : G.p = 1 := by sorry
