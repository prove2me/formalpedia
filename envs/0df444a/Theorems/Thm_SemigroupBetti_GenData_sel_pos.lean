-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel_pos
-- name    : SemigroupBetti.GenData.sel_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:54:14.743694+00:00
-- url     : https://prove2.me/theorems/5a6a7615-5ff6-4d04-bdd9-651b3c86403b
-- title:
--   Gen Data: sel pos
-- statement:
--   The Gen Data construction uses the sel pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L221-L223
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L221-L223

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

theorem SemigroupBetti.GenData.sel_pos {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2) {i : Fin 4}
    (hi : i ∈ K) : 0 < G.sel d K i := by sorry
