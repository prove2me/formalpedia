-- Prove2me | Theorems.Thm_Parikh_simple_height
-- name    : Parikh.simple_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:06.181178+00:00
-- url     : https://prove2.me/theorems/1de83123-c8d6-4a25-bf77-2c8381eeaaf3
-- title:
--   Parikh: simple height
-- statement:
--   Simple complete trees have bounded production height (`lem:simple-height`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L128-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L128-L138

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.simple_height (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) (hs : t.Simple) :
    t.height ≤ (activeNonterminals g).card := by sorry
