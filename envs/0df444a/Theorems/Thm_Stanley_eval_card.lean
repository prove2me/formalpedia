-- Prove2me | Theorems.Thm_Stanley_eval_card
-- name    : Stanley.eval_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:32.95281+00:00
-- url     : https://prove2.me/theorems/025e91b4-e43a-5a68-af62-21aa8c75df17
-- title:
--   Stanley: eval card
-- statement:
--   The Stanley construction uses the eval card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L96-L98
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L96-L98

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

theorem Stanley.eval_card (α : Type v) [Fintype α] :
    (chromaticPolynomial G).eval (Fintype.card α : ℤ) = Fintype.card (G.Coloring α) := by sorry
