-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_nu_eq_sum
-- name    : SemigroupBetti.GenData.nu_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:04.826933+00:00
-- url     : https://prove2.me/theorems/7dc65ba1-d88f-5178-ac4f-abd4735cd7d4
-- title:
--   Gen Data: nu eq sum
-- statement:
--   The Gen Data construction uses the nu eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L95-L97
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L95-L97

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

theorem SemigroupBetti.GenData.nu_eq_sum (z : Fin 4 → ℕ) : G.nu z = z 0 * G.m + z 1 * (G.m + G.a) +
    z 2 * (G.m + G.b) + z 3 * (G.m + G.w) := by sorry
