-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_IsSplit_compl
-- name    : SemigroupBetti.GenData.IsSplit.compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:53:55.789277+00:00
-- url     : https://prove2.me/theorems/c015d317-3f82-59d4-97df-0ab362ef6419
-- title:
--   Is Split: compl
-- statement:
--   The Is Split construction uses the compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L44-L46
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L44-L46

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.IsSplit.compl {d : ℕ} {K : Finset (Fin 4)} (h : G.IsSplit d K) : G.IsSplit d Kᶜ := by sorry
