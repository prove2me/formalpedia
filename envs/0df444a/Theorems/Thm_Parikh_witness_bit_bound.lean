-- Prove2me | Theorems.Thm_Parikh_witness_bit_bound
-- name    : Parikh.witness_bit_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:39.794031+00:00
-- url     : https://prove2.me/theorems/fd1d8111-b7de-4073-8f65-925dc92e5a1b
-- title:
--   Parikh: witness bit bound
-- statement:
--   Numerical entries fit the stated fixed-width bit budget (`eq:bit-bound`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L188-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L188-L233

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Parikh_Construction
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.witness_bit_bound {T : Type*} [Fintype T] (s : GrammarSize)
    (hd : s.terminals = Fintype.card T) (W : Witness T) (h : WithinBounds s W) :
    entryBits s W ≤ s.vectorBits ∧
      (∀ c ∈ W, ∀ a, c.base a < 2 ^ s.coordinateBits) ∧
      (∀ c ∈ W, ∀ p ∈ c.periods, ∀ a, p a < 2 ^ s.coordinateBits) := by sorry
