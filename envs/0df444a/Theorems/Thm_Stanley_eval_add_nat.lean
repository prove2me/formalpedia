-- Prove2me | Theorems.Thm_Stanley_eval_add_nat
-- name    : Stanley.eval_add_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:00.478625+00:00
-- url     : https://prove2.me/theorems/ca19c955-53e9-5465-9d7d-78860a8c5ec2
-- title:
--   Stanley: eval add nat
-- statement:
--   The Stanley construction uses the eval add nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L108-L116
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L108-L116

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution
set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
open Classical

theorem Stanley.eval_add_nat (n m : ℕ) :
    (chromaticPolynomial G).eval ((n : ℤ) + m) =
      ∑ s : Finset V, (chromaticPolynomial (G.induce (s : Set V))).eval (n : ℤ) *
        (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval (m : ℤ) := by sorry
