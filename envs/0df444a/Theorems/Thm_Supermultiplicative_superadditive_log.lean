-- Prove2me | Theorems.Thm_Supermultiplicative_superadditive_log
-- name    : Supermultiplicative.superadditive_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:17.827886+00:00
-- url     : https://prove2.me/theorems/f9a803d8-4e4d-599f-ba09-c426da069925
-- title:
--   Supermultiplicative: superadditive log
-- statement:
--   The logarithm of a positive supermultiplicative sequence is superadditive.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L170-L173
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L170-L173

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open Supermultiplicative
variable {u : ℕ → ℝ}

theorem Supermultiplicative.superadditive_log (h : Supermultiplicative u) (hpos : ∀ n, 0 < u n) :
    Superadditive fun n ↦ Real.log (u n) := by sorry
