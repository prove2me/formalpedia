-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_toricMap_mono
-- name    : SemigroupBetti.GenData.toricMap_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:02.925045+00:00
-- url     : https://prove2.me/theorems/d78f9c03-1a46-420b-9fa1-e5ef401bce8c
-- title:
--   Gen Data: toric Map mono
-- statement:
--   The Gen Data construction uses the toric Map mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L80-L81
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L80-L81

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

theorem SemigroupBetti.GenData.toricMap_mono (z : Fin 4 → ℕ) : toricMap K G.n (mono K z) = Polynomial.X ^ G.nu z := by sorry
