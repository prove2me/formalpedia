-- Prove2me | Theorems.Thm_Parikh_EncodedGrammar_compile_bit_bound
-- name    : Parikh.EncodedGrammar.compile_bit_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:56:18.328346+00:00
-- url     : https://prove2.me/theorems/34ea139a-89ad-44c4-badf-d68ae6663e2b
-- title:
--   Encoded Grammar: compile bit bound
-- statement:
--   The compiled numerical entries satisfy the accepted fixed-width bit budget.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/ExecutableCompiler.lean#L163-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/ExecutableCompiler.lean#L163-L167

module
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
public import Definitions.Def_LeanPool_Parikh_CompilerBounds
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar

theorem Parikh.EncodedGrammar.compile_bit_bound (g : EncodedGrammar) :
    entryBits g.size g.compile ≤ g.size.vectorBits ∧
      (∀ c ∈ g.compile, ∀ a, c.base a < 2 ^ g.size.coordinateBits) ∧
      (∀ c ∈ g.compile, ∀ p ∈ c.periods, ∀ a, p a < 2 ^ g.size.coordinateBits) := by sorry
