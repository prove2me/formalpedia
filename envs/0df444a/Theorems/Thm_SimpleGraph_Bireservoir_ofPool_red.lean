-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_ofPool_red
-- name    : SimpleGraph.Bireservoir.ofPool_red
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:42.014154+00:00
-- url     : https://prove2.me/theorems/576eb9d9-7ba1-5aa2-be68-33dfa16b6bf4
-- title:
--   Bireservoir: of Pool red
-- statement:
--   The starting state has an empty red spine.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L106-L106
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L106-L106

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

theorem SimpleGraph.Bireservoir.ofPool_red (X : Finset V) : (ofPool (G := G) X).red = ∅ := by sorry

attribute [defeq] SimpleGraph.Bireservoir.ofPool_red
