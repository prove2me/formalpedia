-- Prove2me | Theorems.Thm_Stanley_eval_one_induce
-- name    : Stanley.eval_one_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:11.717731+00:00
-- url     : https://prove2.me/theorems/3219a614-23ef-4ee9-a148-02de2aa3184c
-- title:
--   Stanley: eval one induce
-- statement:
--   The Stanley construction uses the eval one induce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L164-L180
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L164-L180

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
omit [Fintype V]

theorem Stanley.eval_one_induce (s : Finset V) :
    (chromaticPolynomial (G.induce (s : Set V))).eval 1 =
      if Independent G (s : Set V) then 1 else 0 := by sorry
