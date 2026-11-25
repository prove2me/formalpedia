-- Prove2me | Theorems.Thm_SimpleGraph_not_ramseyBound_five_three_three
-- name    : SimpleGraph.not_ramseyBound_five_three_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:32:18.063426+00:00
-- url     : https://prove2.me/theorems/bdb8696c-644b-567f-b9be-b2a74e0e4066
-- title:
--   Simple Graph: not ramsey Bound five three three
-- statement:
--   `R(3, 3) > 5`: the five-cycle has no triangle and neither does its complement.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L349-L359
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L349-L359

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

theorem SimpleGraph.not_ramseyBound_five_three_three : ¬RamseyBound 5 3 3 := by sorry
