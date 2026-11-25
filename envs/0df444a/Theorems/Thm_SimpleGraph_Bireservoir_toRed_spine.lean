-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_toRed_spine
-- name    : SimpleGraph.Bireservoir.toRed_spine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:31.654611+00:00
-- url     : https://prove2.me/theorems/6e4944e4-ec08-55c9-bf75-c95b09c682ca
-- title:
--   Bireservoir: to Red spine
-- statement:
--   The red reservoir's spine is the red clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L123-L123
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L123-L123

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

theorem SimpleGraph.Bireservoir.toRed_spine : S.toRed.spine = S.red := by sorry

attribute [defeq] SimpleGraph.Bireservoir.toRed_spine
