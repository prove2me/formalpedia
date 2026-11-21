-- Prove2me | Theorems.Thm_SafetyLivenessDecomposition_append_slice_eq_self
-- name    : SafetyLivenessDecomposition.append_slice_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:43:36.325895+00:00
-- url     : https://prove2.me/theorems/862b59eb-d1f0-4361-a928-45803e4eb317
-- title:
--   Safety Liveness Decomposition: append slice eq self
-- statement:
--   The Safety Liveness Decomposition construction uses the append slice eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/SafetyLivenessDecomposition.lean#L88-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/SafetyLivenessDecomposition.lean#L88-L94

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

theorem SafetyLivenessDecomposition.append_slice_eq_self (σ : InfWord T) (n : ℕ) :
    (σ.slice n).append (fun k => σ (k + n)) = σ := by sorry
