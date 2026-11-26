-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel_antichain
-- name    : SemigroupBetti.GenData.sel_antichain
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:54:32.254561+00:00
-- url     : https://prove2.me/theorems/ee921a81-3269-5653-bd1d-c3c1b262ee70
-- title:
--   Gen Data: sel antichain
-- statement:
--   **Lemma 7.** For a fixed side `K` (a pair), the selected `K`-vectors at distinct split degrees
--   are not comparable: `¬ (z_d ≤ z_{d'})`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L309-L339
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L309-L339

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

theorem SemigroupBetti.GenData.sel_antichain {K : Finset (Fin 4)} (hK : K.card = 2) {d d' : ℕ} (hS : G.IsSplit d K)
    (hS' : G.IsSplit d' K) (hne : d ≠ d') : ¬ G.sel d K ≤ G.sel d' K := by sorry
