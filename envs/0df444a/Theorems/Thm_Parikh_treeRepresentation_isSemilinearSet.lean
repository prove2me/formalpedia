-- Prove2me | Theorems.Thm_Parikh_treeRepresentation_isSemilinearSet
-- name    : Parikh.treeRepresentation_isSemilinearSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:15.470796+00:00
-- url     : https://prove2.me/theorems/6b99118c-832c-49e6-8161-e05565336cf4
-- title:
--   Parikh: tree Representation is Semilinear Set
-- statement:
--   The tree representation is a finite union of the existing linear components.
--   Filtering the finite powerset keeps exactly the activatable context subsets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteRepresentation.lean#L58-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteRepresentation.lean#L58-L80

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Definitions.Def_LeanPool_Parikh_FiniteRepresentation
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.treeRepresentation_isSemilinearSet [Finite T] [DecidableEq T]
    (g : ContextFreeGrammar T) : IsSemilinearSet (treeRepresentation g) := by sorry
