-- Prove2me | Theorems.Thm_Parikh_familyWitness_length_le
-- name    : Parikh.familyWitness_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:04.219511+00:00
-- url     : https://prove2.me/theorems/f7f8094e-24b8-4001-ace1-beb8787458e3
-- title:
--   Parikh: family Witness length le
-- statement:
--   Activation filtering cannot exceed the number of base/subset pairs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteWitness.lean#L54-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteWitness.lean#L54-L61

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [DecidableEq T]

theorem Parikh.familyWitness_length_le (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT)) :
    (familyWitness g bases cycles).length ≤ bases.card * 2 ^ cycles.card := by sorry
