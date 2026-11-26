-- Prove2me | Theorems.Thm_Stanley_AcyclicOrientation_exists_source
-- name    : Stanley.AcyclicOrientation.exists_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:59.212412+00:00
-- url     : https://prove2.me/theorems/dc9d2e2f-b9ea-4542-8c07-52877de0c99e
-- title:
--   Acyclic Orientation: exists source
-- statement:
--   The Acyclic Orientation construction uses the exists source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Orientation.lean#L49-L51
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Orientation.lean#L49-L51

module
public import Definitions.Def_Stanley_Definitions
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_Stanley_Orientation
set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset
universe u
variable {V : Type u} (G : SimpleGraph V)
open Stanley.AcyclicOrientation
variable {G}

theorem Stanley.AcyclicOrientation.exists_source [Nonempty V] (D : AcyclicOrientation G) : ∃ v, D.Source v := by sorry
