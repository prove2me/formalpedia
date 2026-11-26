-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_len_vec
-- name    : SemigroupBetti.GenData.len_vec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:55:36.268963+00:00
-- url     : https://prove2.me/theorems/e63e397d-5662-539b-865b-86df9ae30b46
-- title:
--   Gen Data: len vec
-- statement:
--   The Gen Data construction uses the len vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L92-L93
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L92-L93

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

theorem SemigroupBetti.GenData.len_vec (x0 x1 x2 x3 : ℕ) : len ![x0, x1, x2, x3] = x0 + x1 + x2 + x3 := by sorry
