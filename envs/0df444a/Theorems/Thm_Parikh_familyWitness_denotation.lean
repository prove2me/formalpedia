-- Prove2me | Theorems.Thm_Parikh_familyWitness_denotation
-- name    : Parikh.familyWitness_denotation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:06.061797+00:00
-- url     : https://prove2.me/theorems/ffc3fc2c-e7e4-4908-9e80-19e8d6d12689
-- title:
--   Parikh: family Witness denotation
-- statement:
--   Exact base and cycle families give exactly the grammar's Parikh image.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteWitness.lean#L64-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteWitness.lean#L64-L79

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [DecidableEq T]

theorem Parikh.familyWitness_denotation [Finite T] (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT))
    (hb : ∀ B, B ∈ bases ↔ IsBase g B)
    (hc : ∀ C, C ∈ cycles ↔ IsBoundedCycle g C) :
    (familyWitness g bases cycles).denotation = image g.language := by sorry
