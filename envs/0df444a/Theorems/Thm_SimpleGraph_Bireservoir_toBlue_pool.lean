-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_toBlue_pool
-- name    : SimpleGraph.Bireservoir.toBlue_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:29:00.772571+00:00
-- url     : https://prove2.me/theorems/b2c39b85-bfe0-4ab0-b400-96fcbab58ec3
-- title:
--   Bireservoir: to Blue pool
-- statement:
--   The blue reservoir's pool is the common pool.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L132-L132
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L132-L132

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

theorem SimpleGraph.Bireservoir.toBlue_pool : S.toBlue.pool = S.pool := by sorry

attribute [defeq] SimpleGraph.Bireservoir.toBlue_pool
