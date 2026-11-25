-- Prove2me | Theorems.Thm_SimpleGraph_RamseyBound_not_cliqueFree_or
-- name    : SimpleGraph.RamseyBound.not_cliqueFree_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:42.252494+00:00
-- url     : https://prove2.me/theorems/e2c9924d-35ff-513c-8763-5a3000e76967
-- title:
--   Ramsey Bound: not clique Free or
-- statement:
--   The graph form of the transfer: a graph on at least `n` vertices contains an `r`-clique or an
--   independent `s`-set.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L82-L85
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L82-L85

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_RamseyReservoir_RamseyBound
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {n m r s : ℕ}

theorem SimpleGraph.RamseyBound.not_cliqueFree_or [Fintype V] (h : RamseyBound n r s) (G : SimpleGraph V)
    (hV : n ≤ Fintype.card V) : ¬G.CliqueFree r ∨ ¬Gᶜ.CliqueFree s := by sorry
