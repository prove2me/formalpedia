-- Prove2me | Theorems.Thm_SimpleGraph_RamseyBound_mono_sizes
-- name    : SimpleGraph.RamseyBound.mono_sizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:49.241894+00:00
-- url     : https://prove2.me/theorems/1371c9cc-5ca8-577a-9f1e-67e1b588695d
-- title:
--   Ramsey Bound: mono sizes
-- statement:
--   Smaller targets: a Ramsey bound for `(r, s)` is one for `(r', s')` when `r' ≤ r`, `s' ≤ s`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L219-L225
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L219-L225

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

theorem SimpleGraph.RamseyBound.mono_sizes {n r s r' s' : ℕ} (h : RamseyBound n r s)
    (hr : r' ≤ r) (hs : s' ≤ s) : RamseyBound n r' s' := by sorry
