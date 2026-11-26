-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel_eq_zero
-- name    : SemigroupBetti.GenData.sel_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:54:35.419151+00:00
-- url     : https://prove2.me/theorems/482c64c4-7842-4149-83b2-d4bd4e8c897f
-- title:
--   Gen Data: sel eq zero
-- statement:
--   The Gen Data construction uses the sel eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L225-L228
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L225-L228

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

theorem SemigroupBetti.GenData.sel_eq_zero {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2) {i : Fin 4}
    (hi : i ∉ K) : G.sel d K i = 0 := by sorry
