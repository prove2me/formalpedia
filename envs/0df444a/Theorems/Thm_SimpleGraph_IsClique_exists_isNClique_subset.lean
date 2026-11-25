-- Prove2me | Theorems.Thm_SimpleGraph_IsClique_exists_isNClique_subset
-- name    : SimpleGraph.IsClique.exists_isNClique_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:29:56.47718+00:00
-- url     : https://prove2.me/theorems/5489ad25-2add-570f-b3b2-31b5d3bab0f6
-- title:
--   Is Clique: exists is NClique subset
-- statement:
--   A clique of size at least `r` contains an `r`-clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L213-L216
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L213-L216

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_RamseyBound_exists_isNClique_subset

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}
variable (S : G.Bireservoir)

theorem SimpleGraph.IsClique.exists_isNClique_subset {H : SimpleGraph V} {s : Finset V}
    (hs : H.IsClique (s : Set V)) {r : ℕ} (hr : r ≤ #s) : ∃ t ⊆ s, H.IsNClique r t := by sorry
