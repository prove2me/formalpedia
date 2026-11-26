-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel_of_split
-- name    : SemigroupBetti.GenData.sel_of_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:54:25.394821+00:00
-- url     : https://prove2.me/theorems/b40b5e59-1169-42c8-b618-0fe91a1e195e
-- title:
--   Gen Data: sel of split
-- statement:
--   The selected vectors at a split degree: `ν = d` and support `K`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L214-L216
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L214-L216

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

theorem SemigroupBetti.GenData.sel_of_split {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2) :
    G.nu (G.sel d K) = d ∧ supp (G.sel d K) = K := by sorry
