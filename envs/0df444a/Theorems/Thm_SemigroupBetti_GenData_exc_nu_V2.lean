-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exc_nu_V2
-- name    : SemigroupBetti.GenData.exc_nu_V2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:59.514401+00:00
-- url     : https://prove2.me/theorems/0439ec7a-5cb5-5134-9d0e-7a3472721b45
-- title:
--   Gen Data: exc nu V2
-- statement:
--   `ν(0,0,W-1,0) = ν(0,1,0,W-2)`, both equal to `(W-1) n₂`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L126-L127
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L126-L127

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

theorem SemigroupBetti.GenData.exc_nu_V2 : G.nu ![0, 1, 0, G.W - 2] = (G.W - 1) * G.n 2 := by sorry
