-- Prove2me | Theorems.Thm_Parikh_mem_familyWitness
-- name    : Parikh.mem_familyWitness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:08.322874+00:00
-- url     : https://prove2.me/theorems/69b71dd8-9351-4694-b019-b032d51a3bf2
-- title:
--   Parikh: mem family Witness
-- statement:
--   Component membership retains both its base tree and its selected context subset.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteWitness.lean#L39-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/FiniteWitness.lean#L39-L51

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [DecidableEq T]

theorem Parikh.mem_familyWitness (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT)) (c : Component T) :
    c ∈ familyWitness g bases cycles ↔
      ∃ B ∈ bases, ∃ D : Finset (ParseTree T g.NT),
        D ⊆ cycles ∧ ContextsActivatable g B D ∧ contextComponent B D = c := by sorry
