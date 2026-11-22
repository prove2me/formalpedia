-- Prove2me | Theorems.Thm_Parikh_InsertionSequence_accounting
-- name    : Parikh.InsertionSequence.accounting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:28.793691+00:00
-- url     : https://prove2.me/theorems/352da9fe-a993-4162-a73f-096b8de00248
-- title:
--   Insertion Sequence: accounting
-- statement:
--   Every insertion sequence preserves completeness/root and exactly adds the
--   listed weights and production counts, while taking the union of supports.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/InsertionSequences.lean#L48-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/InsertionSequences.lean#L48-L70

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.InsertionSequence.accounting [DecidableEq T] {g : ContextFreeGrammar T}
    {B t : ParseTree T g.NT} {Cs : List (ParseTree T g.NT)}
    (h : InsertionSequence g B Cs t) (hB : Complete g B) :
    Complete g t ∧ t.root = B.root ∧
      t.weight = B.weight + (Cs.map ParseTree.weight).sum ∧
      t.productionSize = B.productionSize + (Cs.map ParseTree.productionSize).sum ∧
      t.support = B.support ∪ ⋃ C ∈ Cs, C.support := by sorry
