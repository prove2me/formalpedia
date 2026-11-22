-- Prove2me | Theorems.Thm_Parikh_Cycle_root_mem_support
-- name    : Parikh.Cycle.root_mem_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:25.934126+00:00
-- url     : https://prove2.me/theorems/c5ea74fa-398b-4583-9d82-fe916f0541b5
-- title:
--   Cycle: root mem support
-- statement:
--   A nontrivial cycle has a production node at its root (`eq:cycle-root`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/InsertionSequences.lean#L35-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/InsertionSequences.lean#L35-L44

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.Cycle.root_mem_support {g : ContextFreeGrammar T} {C : ParseTree T g.NT}
    {A : g.NT} (hC : Cycle g C A) : A ∈ C.support := by sorry
