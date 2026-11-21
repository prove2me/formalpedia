-- Prove2me | Theorems.Thm_SafetyLivenessDecomposition_slice_get
-- name    : SafetyLivenessDecomposition.slice_get
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:43:36.661289+00:00
-- url     : https://prove2.me/theorems/f6f25083-b47a-4212-b0c5-53486fe07e86
-- title:
--   Safety Liveness Decomposition: slice get
-- statement:
--   The Safety Liveness Decomposition construction uses the slice get property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/SafetyLivenessDecomposition.lean#L77-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/SafetyLivenessDecomposition.lean#L77-L80

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

theorem SafetyLivenessDecomposition.slice_get (σ : InfWord T) (n k : ℕ)
    (hk : k < (σ.slice n).length) :
    (σ.slice n)[k] = σ k := by sorry
