-- Prove2me | Theorems.Thm_Stanley_chromaticPolynomial_iso
-- name    : Stanley.chromaticPolynomial_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:55.242978+00:00
-- url     : https://prove2.me/theorems/24c1c2bf-e75e-4729-8f29-403a24755211
-- title:
--   Stanley: chromatic Polynomial iso
-- statement:
--   The Stanley construction uses the chromatic Polynomial iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L145-L150
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L145-L150

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

theorem Stanley.chromaticPolynomial_iso {W : Type*} [Fintype W] (H : SimpleGraph W) (e : G ≃g H) :
    chromaticPolynomial G = chromaticPolynomial H := by sorry
