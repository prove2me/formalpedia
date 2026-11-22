-- Prove2me | Theorems.Thm_Parikh_ParseTree_norm_weight_eq_length
-- name    : Parikh.ParseTree.norm_weight_eq_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:36.813831+00:00
-- url     : https://prove2.me/theorems/6087d0bc-1077-4c33-a8d2-baa3ac83b9d9
-- title:
--   Parse Tree: norm weight eq length
-- statement:
--   Summing the terminal counts gives the length of a tree's terminal yield.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L89-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L89-L97

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Parikh_Construction
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.ParseTree.norm_weight_eq_length {T N : Type*} [Fintype T] [DecidableEq T]
    (t : ParseTree T N) : norm t.weight = t.yield.length := by sorry
