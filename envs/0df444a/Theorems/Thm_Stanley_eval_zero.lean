-- Prove2me | Theorems.Thm_Stanley_eval_zero
-- name    : Stanley.eval_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:57.653872+00:00
-- url     : https://prove2.me/theorems/3111fd26-9ad4-5341-a37b-ca8d7ef99286
-- title:
--   Stanley: eval zero
-- statement:
--   The Stanley construction uses the eval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L157-L160
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L157-L160

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

theorem Stanley.eval_zero [Nonempty V] : (chromaticPolynomial G).eval 0 = 0 := by sorry
