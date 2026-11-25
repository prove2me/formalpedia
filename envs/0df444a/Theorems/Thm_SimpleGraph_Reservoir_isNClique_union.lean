-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_isNClique_union
-- name    : SimpleGraph.Reservoir.isNClique_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:22.20067+00:00
-- url     : https://prove2.me/theorems/82fcbca1-0c27-4fee-a62b-f1e4f69f884f
-- title:
--   Reservoir: is NClique union
-- statement:
--   **Gluing.** A clique `t` inside the pool extends the spine.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L103-L108
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L103-L108

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Reservoir
variable {G}
variable (R : G.Reservoir)

theorem SimpleGraph.Reservoir.isNClique_union [DecidableEq V] {t : Finset V} {n : ℕ} (ht : G.IsNClique n t)
    (hsub : t ⊆ R.pool) : G.IsNClique (#R.spine + n) (R.spine ∪ t) := by sorry
