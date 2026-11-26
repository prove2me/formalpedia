-- Prove2me | Theorems.Thm_Stanley_convolution
-- name    : Stanley.convolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:53.115543+00:00
-- url     : https://prove2.me/theorems/cc82efec-6a12-4304-b0ca-2866f58c84d7
-- title:
--   Stanley: convolution
-- statement:
--   The Stanley construction uses the convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L119-L142
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean#L119-L142

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

theorem Stanley.convolution (a b : ℤ) :
    (chromaticPolynomial G).eval (a + b) =
      ∑ s : Finset V, (chromaticPolynomial (G.induce (s : Set V))).eval a *
        (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval b := by sorry
