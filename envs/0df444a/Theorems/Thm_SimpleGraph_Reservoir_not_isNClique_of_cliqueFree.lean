-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_not_isNClique_of_cliqueFree
-- name    : SimpleGraph.Reservoir.not_isNClique_of_cliqueFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:04.477936+00:00
-- url     : https://prove2.me/theorems/c5844084-f363-4a73-a05b-e4b8739c737f
-- title:
--   Reservoir: not is NClique of clique Free
-- statement:
--   If `G` has no `(#spine + n)`-clique, the pool contains no `n`-clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L111-L114
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L111-L114

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

theorem SimpleGraph.Reservoir.not_isNClique_of_cliqueFree {n : ℕ} (hG : G.CliqueFree (#R.spine + n)) {t : Finset V}
    (hsub : t ⊆ R.pool) : ¬G.IsNClique n t := by sorry
