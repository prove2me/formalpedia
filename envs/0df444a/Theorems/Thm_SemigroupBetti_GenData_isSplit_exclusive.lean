-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_isSplit_exclusive
-- name    : SemigroupBetti.GenData.isSplit_exclusive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:27.034837+00:00
-- url     : https://prove2.me/theorems/26d7cfbd-2f91-5f52-b6fc-957942ec6868
-- title:
--   Gen Data: is Split exclusive
-- statement:
--   The Gen Data construction uses the is Split exclusive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L247-L253
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L247-L253

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

theorem SemigroupBetti.GenData.isSplit_exclusive {d : ℕ} {K L : Finset (Fin 4)} (hK : G.IsSplit d K) (hL : G.IsSplit d L)
    {i : Fin 4} (hiK : i ∈ K) (hiL : i ∈ L) : K = L := by sorry
