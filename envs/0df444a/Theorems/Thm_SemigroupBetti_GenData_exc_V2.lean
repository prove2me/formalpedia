-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exc_V2
-- name    : SemigroupBetti.GenData.exc_V2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:54.721196+00:00
-- url     : https://prove2.me/theorems/95f1c924-d546-5124-a21f-852e4ff39a05
-- title:
--   Gen Data: exc V2
-- statement:
--   The Gen Data construction uses the exc V2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L119-L123
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L119-L123

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

theorem SemigroupBetti.GenData.exc_V2 : G.V2 = ![0, 1, 0, G.W - 2] := by sorry
