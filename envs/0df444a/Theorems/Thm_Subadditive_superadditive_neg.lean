-- Prove2me | Theorems.Thm_Subadditive_superadditive_neg
-- name    : Subadditive.superadditive_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:12.475581+00:00
-- url     : https://prove2.me/theorems/20b85767-5a36-44fb-bd3e-fab3e9897b32
-- title:
--   Subadditive: superadditive neg
-- statement:
--   The negation of a subadditive sequence is superadditive.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L99-L100
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L99-L100

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

theorem Subadditive.superadditive_neg {u : ℕ → ℝ} (h : Subadditive u) :
    Superadditive fun n ↦ -u n := by sorry
