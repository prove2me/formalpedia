-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_IsWinning_exists_pivot
-- name    : SimpleGraph.Bireservoir.IsWinning.exists_pivot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:16.150634+00:00
-- url     : https://prove2.me/theorems/acbd9620-e306-5476-a7b2-cd0072b6fe95
-- title:
--   Is Winning: exists pivot
-- statement:
--   **The potential never runs out.** From a winning state whose spines are both short of the
--   target, one of the two pivots at some pool vertex is again winning.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L256-L271
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L256-L271

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
variable {S}

theorem SimpleGraph.Bireservoir.IsWinning.exists_pivot [DecidableEq V] [DecidableRel G.Adj] {R : ℕ → ℕ → ℕ} {r s : ℕ}
    (hR : IsPascal R) (hS : S.IsWinning R r s) (hr : #S.red < r) (hs : #S.blue < s) :
    ∃ v, ∃ hv : v ∈ S.pool,
      (S.redPivot hv).IsWinning R r s ∨ (S.bluePivot hv).IsWinning R r s := by sorry
