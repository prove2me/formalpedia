-- Prove2me | Theorems.Thm_Parikh_one_linear
-- name    : Parikh.one_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:09.674227+00:00
-- url     : https://prove2.me/theorems/ddc9626b-4f9d-4efe-8faf-e55ebb897005
-- title:
--   Parikh: one linear
-- statement:
--   The weights obtained using exactly an activatable family of contexts form
--   one linear component (`prop:one-linear`).
--   Every selected context must occur at least once. These first copies are included
--   in the component's base; its period coefficients count additional copies.
--   The equality proves both that insertion yields only these vectors and that
--   every choice of coefficients can be realized by an insertion sequence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L309-L356
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L309-L356

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.one_linear {T : Type*} [DecidableEq T] (g : ContextFreeGrammar T)
    (B : ParseTree T g.NT) (D : Finset (ParseTree T g.NT))
    (hB : Complete g B) (hD : ContextsActivatable g B D) :
    {v | ∃ t Cs, InsertionSequence g B Cs t ∧
      (∀ C, C ∈ Cs ↔ C ∈ D) ∧ t.weight = v} =
      (contextComponent B D).denotation := by sorry
