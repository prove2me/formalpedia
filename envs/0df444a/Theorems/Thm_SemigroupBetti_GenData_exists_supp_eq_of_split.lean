-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exists_supp_eq_of_split
-- name    : SemigroupBetti.GenData.exists_supp_eq_of_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:25.568586+00:00
-- url     : https://prove2.me/theorems/4450f391-7f3c-49f0-aa5f-72fae9302b4d
-- title:
--   Gen Data: exists supp eq of split
-- statement:
--   If `d` splits along a pair `K` then it has a factorization with support exactly `K`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L173-L177
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L173-L177

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

theorem SemigroupBetti.GenData.exists_supp_eq_of_split {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K)
    (hK : K.card = 2) : ∃ z : Fin 4 → ℕ, G.nu z = d ∧ supp z = K := by sorry
