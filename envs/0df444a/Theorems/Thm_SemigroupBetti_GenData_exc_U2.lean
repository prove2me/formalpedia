-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exc_U2
-- name    : SemigroupBetti.GenData.exc_U2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:26.385483+00:00
-- url     : https://prove2.me/theorems/d845a1d6-eaac-45ca-93cd-fb05a3b57089
-- title:
--   Gen Data: exc U2
-- statement:
--   The Gen Data construction uses the exc U2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L116-L117
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L116-L117

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

theorem SemigroupBetti.GenData.exc_U2 : G.U2 = Pi.single 2 (G.W - 1) := by sorry
