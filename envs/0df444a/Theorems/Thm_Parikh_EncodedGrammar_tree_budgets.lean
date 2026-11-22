-- Prove2me | Theorems.Thm_Parikh_EncodedGrammar_tree_budgets
-- name    : Parikh.EncodedGrammar.tree_budgets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:53:17.891624+00:00
-- url     : https://prove2.me/theorems/aab240e8-7249-40f7-810d-183616a5e4aa
-- title:
--   Encoded Grammar: tree budgets
-- statement:
--   The executable exact families satisfy the declared syntax budgets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerBounds.lean#L31-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerBounds.lean#L31-L87

module
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Definitions.Def_LeanPool_Parikh_CompilerBounds
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar

theorem Parikh.EncodedGrammar.tree_budgets (g : EncodedGrammar) :
    g.baseTrees.length ≤ g.size.trees ∧ g.cycleTrees.length ≤ g.size.trees ∧
      ∀ t, IsBase g.decode t ∨ IsBoundedCycle g.decode t → norm t.weight ≤ g.size.positions := by sorry
