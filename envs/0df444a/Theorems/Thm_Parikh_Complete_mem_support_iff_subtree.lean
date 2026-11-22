-- Prove2me | Theorems.Thm_Parikh_Complete_mem_support_iff_subtree
-- name    : Parikh.Complete.mem_support_iff_subtree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:42.365063+00:00
-- url     : https://prove2.me/theorems/9a53a1ff-ecb1-4dbc-93ee-10d5d433de23
-- title:
--   Complete: mem support iff subtree
-- statement:
--   In a complete tree, support is exactly the labels of nonterminal-rooted subtrees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreeReplacement.lean#L55-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreeReplacement.lean#L55-L89

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}

theorem Parikh.Complete.mem_support_iff_subtree {g : ContextFreeGrammar T}
    {t : ParseTree T g.NT} (ht : Complete g t) (A : g.NT) :
    A ∈ t.support ↔ ∃ q u, t.subtree q = some u ∧ u.root = .nonterminal A := by sorry
