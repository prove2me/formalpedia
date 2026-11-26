-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_nu_single
-- name    : SemigroupBetti.GenData.nu_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:02.266697+00:00
-- url     : https://prove2.me/theorems/7d933415-f462-4cdc-ae9c-02ea16b0a42b
-- title:
--   Gen Data: nu single
-- statement:
--   The Gen Data construction uses the nu single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L124-L129
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L124-L129

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.nu_single (i : Fin 4) (k : ℕ) : G.nu (Pi.single i k) = k * G.n i := by sorry
