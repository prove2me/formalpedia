-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_one_le_g
-- name    : SemigroupBetti.GenData.one_le_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:48.226486+00:00
-- url     : https://prove2.me/theorems/8d2ea987-6ae4-4bf8-864a-98e6679e06ba
-- title:
--   Gen Data: one le g
-- statement:
--   The Gen Data construction uses the one le g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L167-L167
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L167-L167

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

theorem SemigroupBetti.GenData.one_le_g : 1 ≤ G.g := by sorry
