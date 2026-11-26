-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_single_le_nu
-- name    : SemigroupBetti.GenData.single_le_nu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:41.104409+00:00
-- url     : https://prove2.me/theorems/cc0b25eb-586b-5936-b60a-5481d5d15829
-- title:
--   Gen Data: single le nu
-- statement:
--   The Gen Data construction uses the single le nu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L137-L140
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L137-L140

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

theorem SemigroupBetti.GenData.single_le_nu (z : Fin 4 → ℕ) (i : Fin 4) : z i * G.n i ≤ G.nu z := by sorry
