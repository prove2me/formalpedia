-- Prove2me | Theorems.Thm_Parikh_Complete_subtree_context
-- name    : Parikh.Complete.subtree_context
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:30.604283+00:00
-- url     : https://prove2.me/theorems/88c7a918-2d46-42a5-81d1-e7c7ee5cfc07
-- title:
--   Complete: subtree context
-- statement:
--   A selected nonterminal occurrence can be cut out and replaced through its
--   outer one-hole context. The selected subtree and all side branches are complete.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreeReplacement.lean#L93-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreeReplacement.lean#L93-L147

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}

theorem Parikh.Complete.subtree_context {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Complete g t) (q : List ℕ) (u : ParseTree T g.NT)
    (hpos : t.subtree q = some u) (A : g.NT) (hu : u.root = .nonterminal A) :
    Complete g u ∧ ∃ E, OneHole g E A ∧ E.root = t.root ∧ E.plug u = t ∧
      ∀ v, t.replaceAt q v = some (E.plug v) := by sorry
