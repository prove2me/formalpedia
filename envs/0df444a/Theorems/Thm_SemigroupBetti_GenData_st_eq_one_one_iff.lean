-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_st_eq_one_one_iff
-- name    : SemigroupBetti.GenData.st_eq_one_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:04:22.57397+00:00
-- url     : https://prove2.me/theorems/cead042c-bbbd-5cf6-889d-1c9f260902d4
-- title:
--   Gen Data: st eq one one iff
-- statement:
--   The exceptional case `(s,t) = (1,1)` is exactly `(A, B) = (1, W - 1)`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Arith.lean#L44-L47
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Arith.lean#L44-L47

module
public import Definitions.Def_SemigroupBetti_Antichain
public import Definitions.Def_SemigroupBetti_Arith
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.st_eq_one_one_iff : (G.s, G.t) = (1, 1) ↔ G.A = 1 ∧ G.B = G.W - 1 := by sorry
