-- Prove2me | Theorems.Thm_SimpleGraph_isPascal_choose
-- name    : SimpleGraph.isPascal_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:28.525777+00:00
-- url     : https://prove2.me/theorems/238fb961-6265-580e-8444-32db5ff46c70
-- title:
--   Simple Graph: is Pascal choose
-- statement:
--   The binomial threshold `C(a + b - 2, a - 1)`, extended by zero when `a = 0` or `b = 0`,
--   satisfies Pascal's inequality.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L320-L333
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L320-L333

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

theorem SimpleGraph.isPascal_choose :
    IsPascal fun a b => if a = 0 ∨ b = 0 then 0 else (a + b - 2).choose (a - 1) := by sorry
