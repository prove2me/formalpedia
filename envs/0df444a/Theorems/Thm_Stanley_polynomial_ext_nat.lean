-- Prove2me | Theorems.Thm_Stanley_polynomial_ext_nat
-- name    : Stanley.polynomial_ext_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:37.294872+00:00
-- url     : https://prove2.me/theorems/a8a4c2a6-9b3c-41b9-8d94-9506ef82308a
-- title:
--   Stanley: polynomial ext nat
-- statement:
--   The Stanley construction uses the polynomial ext nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L100-L105
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L100-L105

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

theorem Stanley.polynomial_ext_nat (p q : ℤ[X])
    (h : ∀ n : ℕ, p.eval (n : ℤ) = q.eval (n : ℤ)) : p = q := by sorry
