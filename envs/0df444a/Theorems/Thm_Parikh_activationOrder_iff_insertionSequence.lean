-- Prove2me | Theorems.Thm_Parikh_activationOrder_iff_insertionSequence
-- name    : Parikh.activationOrder_iff_insertionSequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:51.033986+00:00
-- url     : https://prove2.me/theorems/fb78900c-ba69-46b7-8f4a-f07480bd0952
-- title:
--   Parikh: activation Order iff insertion Sequence
-- statement:
--   With matching cycles, enabled support transitions are exactly realizable
--   tree insertion sequences (`lem:activation-realize`). Repeated cycles are allowed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L181-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L181-L208

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

theorem Parikh.activationOrder_iff_insertionSequence {T : Type*} {g : ContextFreeGrammar T}
    (roots : ParseTree T g.NT → g.NT) (B : ParseTree T g.NT)
    (Cs : List (ParseTree T g.NT)) (hB : Complete g B)
    (hCs : ∀ C ∈ Cs, Cycle g C (roots C)) :
    ActivationOrder roots ParseTree.support B.support Cs ↔
      ∃ t, InsertionSequence g B Cs t := by sorry
