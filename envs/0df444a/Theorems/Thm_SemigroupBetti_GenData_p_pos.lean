-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_p_pos
-- name    : SemigroupBetti.GenData.p_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:55:49.3528+00:00
-- url     : https://prove2.me/theorems/69559ef6-20ae-4242-8ddf-a00e7cee95fd
-- title:
--   Gen Data: p pos
-- statement:
--   The Gen Data construction uses the p pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L47-L51
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L47-L51

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.p_pos : 1 ≤ G.p := by sorry
