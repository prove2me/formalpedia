-- Prove2me | Theorems.Thm_SafetyLivenessDecomposition_slice_length
-- name    : SafetyLivenessDecomposition.slice_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:43:35.449378+00:00
-- url     : https://prove2.me/theorems/92370293-dcde-4194-8629-32f1c2926c5f
-- title:
--   Safety Liveness Decomposition: slice length
-- statement:
--   The Safety Liveness Decomposition construction uses the slice length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/SafetyLivenessDecomposition.lean#L74-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/SafetyLivenessDecomposition.lean#L74-L75

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Finiteness.Attr
public import Definitions.Def_LeanPool_LeanModelChecking_SafetyLivenessDecomposition
set_option autoImplicit true
@[expose] public section
public section
open SafetyLivenessDecomposition
variable {T : Type u}

theorem SafetyLivenessDecomposition.slice_length (σ : InfWord T) (n : ℕ) : (σ.slice n).length = n := by sorry
