-- Prove2me | Theorems.Thm_Parikh_contextActivation_correct
-- name    : Parikh.contextActivation_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:45.596918+00:00
-- url     : https://prove2.me/theorems/a09106c0-95e0-43d4-8c71-b4260ed51788
-- title:
--   Parikh: context Activation correct
-- statement:
--   For a family of cycles, the executable support test is exactly the accepted
--   grammar activation predicate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerSupport.lean#L131-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerSupport.lean#L131-L167

module
public import Definitions.Def_LeanPool_Parikh_ActivationAlgorithm
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.contextActivation_correct {T : Type*} (g : ContextFreeGrammar T)
    [DecidableEq g.NT] [DecidableEq (ParseTree T g.NT)]
    (B : ParseTree T g.NT) (D : List (ParseTree T g.NT))
    (hD : ∀ C ∈ D, ∃ A, Cycle g C A) :
    contextActivation g B D = true ↔ ContextsActivatable g B D.toFinset := by sorry
