-- Prove2me | Theorems.Thm_Stanley_acyclic_count_eq
-- name    : Stanley.acyclic_count_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:03:03.81616+00:00
-- url     : https://prove2.me/theorems/4677aba3-8aab-4e9b-b9fa-9fdc360f976f
-- title:
--   Stanley: acyclic count eq
-- statement:
--   The absolute value of the evaluation at -1 counts acyclic orientations.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Reciprocity.lean#L88-L92
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Reciprocity.lean#L88-L92

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

theorem Stanley.acyclic_count_eq :
    (-1 : ℤ) ^ Fintype.card V * (chromaticPolynomial G).eval (-1) =
      orientationCount G := by sorry
