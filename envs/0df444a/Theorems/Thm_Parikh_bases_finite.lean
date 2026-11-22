-- Prove2me | Theorems.Thm_Parikh_bases_finite
-- name    : Parikh.bases_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:14.466795+00:00
-- url     : https://prove2.me/theorems/2f89974f-534a-4bf7-b2ed-0ebb2d629f5f
-- title:
--   Parikh: bases finite
-- statement:
--   Simple complete start trees form a finite family over arbitrary nonterminals.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteRepresentation.lean#L37-L41
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteRepresentation.lean#L37-L41

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Definitions.Def_LeanPool_Parikh_FiniteRepresentation
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.bases_finite [Finite T] (g : ContextFreeGrammar T) :
    {B : ParseTree T g.NT | IsBase g B}.Finite := by sorry
