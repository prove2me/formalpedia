-- Prove2me | Theorems.Thm_Stanley_eval_neg_one
-- name    : Stanley.eval_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:57:00.893614+00:00
-- url     : https://prove2.me/theorems/b7dc98c5-3f9f-5e10-abf5-e2158caccdc6
-- title:
--   Stanley: eval neg one
-- statement:
--   Stanley's acyclic-orientation identity, expressed as a signed integer evaluation.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/NegOne.lean#L83-L138
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/NegOne.lean#L83-L138

module
public import Definitions.Def_Stanley_Convolution
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Stanley_NegOne
set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)

theorem Stanley.eval_neg_one : (chromaticPolynomial G).eval (-1) =
    (-1 : ℤ) ^ Fintype.card V * orientationCount G := by sorry
