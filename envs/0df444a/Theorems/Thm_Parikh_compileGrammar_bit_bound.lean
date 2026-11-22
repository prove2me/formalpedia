-- Prove2me | Theorems.Thm_Parikh_compileGrammar_bit_bound
-- name    : Parikh.compileGrammar_bit_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:57:06.498859+00:00
-- url     : https://prove2.me/theorems/befddc07-54a2-4092-996a-da084df2cf6c
-- title:
--   Parikh: compile Grammar bit bound
-- statement:
--   The computed coordinates fit the fixed-width numerical bit budget.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L112-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L112-L116

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.compileGrammar_bit_bound (g : EncodedGrammar) :
    entryBits g.size (compileGrammar g) ≤ g.size.vectorBits ∧
      (∀ c ∈ compileGrammar g, ∀ a, c.base a < 2 ^ g.size.coordinateBits) ∧
      (∀ c ∈ compileGrammar g, ∀ p ∈ c.periods, ∀ a, p a < 2 ^ g.size.coordinateBits) := by sorry
