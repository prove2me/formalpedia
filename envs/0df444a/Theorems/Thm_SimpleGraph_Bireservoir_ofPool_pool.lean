-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_ofPool_pool
-- name    : SimpleGraph.Bireservoir.ofPool_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:59.463594+00:00
-- url     : https://prove2.me/theorems/ade48e31-c488-4e46-be14-62c598933d39
-- title:
--   Bireservoir: of Pool pool
-- statement:
--   The starting state's pool is the given set.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L112-L112
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L112-L112

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool


set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}

theorem SimpleGraph.Bireservoir.ofPool_pool (X : Finset V) : (ofPool (G := G) X).pool = X := by sorry

attribute [defeq] SimpleGraph.Bireservoir.ofPool_pool
