-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exc_coprime
-- name    : SemigroupBetti.GenData.exc_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:05:55.527145+00:00
-- url     : https://prove2.me/theorems/d7415316-0d0a-4b99-afea-c1deaaebbb91
-- title:
--   Gen Data: exc coprime
-- statement:
--   `gcd(n₂, n₃) = 1` in the exceptional family.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L130-L148
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L130-L148

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

theorem SemigroupBetti.GenData.exc_coprime : Nat.Coprime (G.n 3) (G.n 2) := by sorry
