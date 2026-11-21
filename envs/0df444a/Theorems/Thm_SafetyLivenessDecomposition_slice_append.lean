-- Prove2me | Theorems.Thm_SafetyLivenessDecomposition_slice_append
-- name    : SafetyLivenessDecomposition.slice_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:43:36.812097+00:00
-- url     : https://prove2.me/theorems/02af3cdc-80eb-4a83-8bc1-c8065af1d4b0
-- title:
--   Safety Liveness Decomposition: slice append
-- statement:
--   The Safety Liveness Decomposition construction uses the slice append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/SafetyLivenessDecomposition.lean#L82-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/SafetyLivenessDecomposition.lean#L82-L86

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

theorem SafetyLivenessDecomposition.slice_append (α : FinWord T) (β : InfWord T) :
    (α.append β).slice α.length = α := by sorry
