-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_card_redPivot_red
-- name    : SimpleGraph.Bireservoir.card_redPivot_red
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:07.763044+00:00
-- url     : https://prove2.me/theorems/3843cf3a-4715-52eb-8790-29d6b9883b6d
-- title:
--   Bireservoir: card red Pivot red
-- statement:
--   A red pivot grows the red clique by one.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L181-L182
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L181-L182

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
variable [DecidableEq V] [DecidableRel G.Adj] {v : V} (hv : v ∈ S.pool)

theorem SimpleGraph.Bireservoir.card_redPivot_red : #(S.redPivot hv).red = #S.red + 1 := by sorry
