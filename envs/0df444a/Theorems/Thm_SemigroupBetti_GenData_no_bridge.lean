-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_no_bridge
-- name    : SemigroupBetti.GenData.no_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:54:27.913103+00:00
-- url     : https://prove2.me/theorems/46bcc737-06f9-55c0-9f4a-5e5abc4f9ade
-- title:
--   Gen Data: no bridge
-- statement:
--   **No bridge across a split.** If `d` splits along `K`, `z` is positive somewhere in `K`, `y`
--   somewhere in `Kᶜ`, then no factorization of `d` shares a variable with both.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L57-L69
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L57-L69

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

theorem SemigroupBetti.GenData.no_bridge {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) {z y b : Fin 4 → ℕ}
    (hz : G.nu z = d) (hy : G.nu y = d) (hb : G.nu b = d) {i j : Fin 4} (hi : i ∈ K)
    (hzi : 0 < z i) (hj : j ∉ K) (hyj : 0 < y j) (hbz : SharesVar b z) (hby : SharesVar b y) :
    False := by sorry
