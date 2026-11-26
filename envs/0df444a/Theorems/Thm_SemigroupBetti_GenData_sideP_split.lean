-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sideP_split
-- name    : SemigroupBetti.GenData.sideP_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:05:27.359474+00:00
-- url     : https://prove2.me/theorems/e9fea78b-c0ff-55d1-a13e-5fd60d7aaf28
-- title:
--   Gen Data: side P split
-- statement:
--   The Gen Data construction uses the side P split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L154-L156
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L154-L156

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.sideP_split {d : ℕ} (hd : d ∈ G.famP) : G.IsSplit d {2, 3} := by sorry
