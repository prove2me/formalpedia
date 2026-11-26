-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_mono_sub_mem_toricKer
-- name    : SemigroupBetti.GenData.mono_sub_mem_toricKer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:19.67086+00:00
-- url     : https://prove2.me/theorems/bd82a252-2cef-58f7-852d-fbad4e97a17e
-- title:
--   Gen Data: mono sub mem toric Ker
-- statement:
--   The Gen Data construction uses the mono sub mem toric Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L91-L93
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L91-L93

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

theorem SemigroupBetti.GenData.mono_sub_mem_toricKer {z z' : Fin 4 → ℕ} (h : G.nu z = G.nu z') :
    mono K z - mono K z' ∈ G.toricKer K := by sorry
