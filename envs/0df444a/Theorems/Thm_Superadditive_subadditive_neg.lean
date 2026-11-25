-- Prove2me | Theorems.Thm_Superadditive_subadditive_neg
-- name    : Superadditive.subadditive_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:08.349892+00:00
-- url     : https://prove2.me/theorems/93e957dd-6f28-4b62-875d-cb33b52ef3b7
-- title:
--   Superadditive: subadditive neg
-- statement:
--   The negation of a superadditive sequence is subadditive.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L103-L104
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L103-L104

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

theorem Superadditive.subadditive_neg {u : ℕ → ℝ} (h : Superadditive u) :
    Subadditive fun n ↦ -u n := by sorry
