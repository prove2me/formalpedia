-- Prove2me | Theorems.Thm_Parikh_derives_iff_tree
-- name    : Parikh.derives_iff_tree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:13.827449+00:00
-- url     : https://prove2.me/theorems/fcf4e702-47cf-420e-a0b6-2aa57c5e613e
-- title:
--   Parikh: derives iff tree
-- statement:
--   Concrete bridge to Mathlib's derivation relation, for every root (`prop:tree-word`,
--   appendix A).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L477-L490
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L477-L490

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
variable {N : Type*}

theorem Parikh.derives_iff_tree (g : ContextFreeGrammar T) (A : g.NT) (w : List T) :
    g.Derives [.nonterminal A] (w.map Symbol.terminal) ↔
      ∃ t : ParseTree T g.NT,
        Complete g t ∧ t.root = .nonterminal A ∧ t.yield = w := by sorry
