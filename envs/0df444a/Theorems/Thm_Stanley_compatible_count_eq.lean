-- Prove2me | Theorems.Thm_Stanley_compatible_count_eq
-- name    : Stanley.compatible_count_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:05.224578+00:00
-- url     : https://prove2.me/theorems/e9bac288-39ea-5f27-852e-b2fd715da747
-- title:
--   Stanley: compatible count eq
-- statement:
--   The signed negative evaluation counts compatible orientation/coloring pairs.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Reciprocity.lean#L81-L85
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Reciprocity.lean#L81-L85

module
public import Definitions.Def_Stanley_Compatible
public import Mathlib.Tactic.Ring
public import Definitions.Def_Stanley_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)

theorem Stanley.compatible_count_eq (k : ℕ) :
    (-1 : ℤ) ^ Fintype.card V * (chromaticPolynomial G).eval (-(k : ℤ)) =
      compatibleCount G k := by sorry
