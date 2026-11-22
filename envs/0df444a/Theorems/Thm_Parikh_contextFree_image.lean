-- Prove2me | Theorems.Thm_Parikh_contextFree_image
-- name    : Parikh.contextFree_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:59.601003+00:00
-- url     : https://prove2.me/theorems/e30af428-0576-4cb9-bdf3-a9e0a0480732
-- title:
--   Parikh: context Free image
-- statement:
--   Language-level specialization using Mathlib's context-free predicate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L58-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L58-L61

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.contextFree_image [Finite T] [DecidableEq T] (L : Language T) (hL : L.IsContextFree) :
    IsSemilinearSet (image L) := by sorry
