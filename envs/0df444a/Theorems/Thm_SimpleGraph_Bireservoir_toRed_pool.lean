-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_toRed_pool
-- name    : SimpleGraph.Bireservoir.toRed_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:50.427943+00:00
-- url     : https://prove2.me/theorems/09c6175f-0dd2-5a62-b6c8-cc3d277bf121
-- title:
--   Bireservoir: to Red pool
-- statement:
--   The red reservoir's pool is the common pool.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L126-L126
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L126-L126

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}
variable (S : G.Bireservoir)

theorem SimpleGraph.Bireservoir.toRed_pool : S.toRed.pool = S.pool := by sorry

attribute [defeq] SimpleGraph.Bireservoir.toRed_pool
