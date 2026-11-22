-- Prove2me | Theorems.Thm_Parikh_ParseTree_subtree_replacement
-- name    : Parikh.ParseTree.subtree_replacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:55.575496+00:00
-- url     : https://prove2.me/theorems/9b19b1f4-2d31-440a-a46e-2f483bdaf35a
-- title:
--   Parse Tree: subtree replacement
-- statement:
--   Replacement retains the selected position and can be undone exactly.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L56-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L56-L79

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
open Parikh.ParseTree

theorem Parikh.ParseTree.subtree_replacement (t : ParseTree T N) (q : List ℕ) (u v : ParseTree T N)
    (hpos : t.subtree q = some u) :
    ∃ t', t.replaceAt q v = some t' ∧ t'.subtree q = some v ∧
      t'.replaceAt q u = some t := by sorry
