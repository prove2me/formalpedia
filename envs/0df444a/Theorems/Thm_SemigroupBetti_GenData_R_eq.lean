-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_R_eq
-- name    : SemigroupBetti.GenData.R_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:57:48.965898+00:00
-- url     : https://prove2.me/theorems/69b7a869-1bbb-4213-a63e-652c4e4dd641
-- title:
--   Gen Data: R eq
-- statement:
--   The Gen Data construction uses the R eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L64-L65
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L64-L65

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

theorem SemigroupBetti.GenData.R_eq : G.R = G.W - max G.s G.t := by sorry
