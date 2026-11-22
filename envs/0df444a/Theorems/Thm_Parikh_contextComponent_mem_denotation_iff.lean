-- Prove2me | Theorems.Thm_Parikh_contextComponent_mem_denotation_iff
-- name    : Parikh.contextComponent.mem_denotation_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:00.728736+00:00
-- url     : https://prove2.me/theorems/009a407c-470c-4c4c-b098-5e0ed4c53cc2
-- title:
--   context Component: mem denotation iff
-- statement:
--   Reindex the period list by its context identities (`eq:component`).
--   Equal or zero weights retain independent natural coefficients.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L269-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L269-L295

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.contextComponent.mem_denotation_iff {T N : Type*} [DecidableEq T]
    (B : ParseTree T N) (D : Finset (ParseTree T N)) (v : Vector T) :
    v ∈ (contextComponent B D).denotation ↔
      ∃ k : ParseTree T N → ℕ,
        v = (B.weight + ∑ C ∈ D, C.weight) + ∑ C ∈ D, k C • C.weight := by sorry
