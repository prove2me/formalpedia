-- Prove2me | Theorems.Thm_Stanley_chromaticPolynomial_eq_external
-- name    : Stanley.chromaticPolynomial_eq_external
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:01.276187+00:00
-- url     : https://prove2.me/theorems/766868b5-c763-4c3f-b1bb-1e0d35b8a6c5
-- title:
--   Stanley: chromatic Polynomial eq external
-- statement:
--   The Stanley construction uses the chromatic Polynomial eq external property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L83-L94
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L83-L94

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

theorem Stanley.chromaticPolynomial_eq_external : chromaticPolynomial G = G.ChromaticPolynomial ℤ := by sorry
