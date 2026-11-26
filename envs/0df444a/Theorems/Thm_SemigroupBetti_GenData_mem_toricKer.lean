-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_mem_toricKer
-- name    : SemigroupBetti.GenData.mem_toricKer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:53:25.731169+00:00
-- url     : https://prove2.me/theorems/c52cc7dd-736c-465a-ac2a-b46cb816427f
-- title:
--   Gen Data: mem toric Ker
-- statement:
--   The Gen Data construction uses the mem toric Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L88-L89
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L88-L89

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]

theorem SemigroupBetti.GenData.mem_toricKer {f : MvPolynomial (Fin 4) K} : f ∈ G.toricKer K ↔ toricMap K G.n f = 0 := by sorry
