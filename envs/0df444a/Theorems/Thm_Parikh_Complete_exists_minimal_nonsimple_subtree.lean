-- Prove2me | Theorems.Thm_Parikh_Complete_exists_minimal_nonsimple_subtree
-- name    : Parikh.Complete.exists_minimal_nonsimple_subtree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:57.175263+00:00
-- url     : https://prove2.me/theorems/681782b1-ed73-47da-9266-a052106e32e4
-- title:
--   Complete: exists minimal nonsimple subtree
-- statement:
--   Descend through non-simple children until every child is simple. This selects
--   the source's minimal non-simple occurrence without a finite ambient alphabet.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L124-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L124-L142

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}

theorem Parikh.Complete.exists_minimal_nonsimple_subtree {g : ContextFreeGrammar T}
    {t : ParseTree T g.NT} (ht : Complete g t) (hs : ¬ t.Simple) :
    ∃ q r cs, t.subtree q = some (.node r cs) ∧ Complete g (.node r cs) ∧
      ¬ (ParseTree.node r cs).Simple ∧ ∀ c ∈ cs, c.Simple := by sorry
