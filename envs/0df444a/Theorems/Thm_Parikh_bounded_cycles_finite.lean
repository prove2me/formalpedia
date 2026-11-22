-- Prove2me | Theorems.Thm_Parikh_bounded_cycles_finite
-- name    : Parikh.bounded_cycles_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:12.387774+00:00
-- url     : https://prove2.me/theorems/674dd314-d472-4bd7-8d92-13e2ac1d0c7e
-- title:
--   Parikh: bounded cycles finite
-- statement:
--   A cycle's unique hole is active because its matching root is a production
--   label. Thus the bounded-cycle family is finite even with infinite nonterminals.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteRepresentation.lean#L45-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteRepresentation.lean#L45-L54

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Definitions.Def_LeanPool_Parikh_FiniteRepresentation
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.bounded_cycles_finite [Finite T] (g : ContextFreeGrammar T) :
    {C : ParseTree T g.NT | IsBoundedCycle g C}.Finite := by sorry
