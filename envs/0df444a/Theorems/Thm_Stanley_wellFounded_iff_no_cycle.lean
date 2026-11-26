-- Prove2me | Theorems.Thm_Stanley_wellFounded_iff_no_cycle
-- name    : Stanley.wellFounded_iff_no_cycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:57.002265+00:00
-- url     : https://prove2.me/theorems/3979db1d-b518-5266-bd01-3a72f43cddb8
-- title:
--   Stanley: well Founded iff no cycle
-- statement:
--   On finite types, well-foundedness is equivalent to having no directed cycle.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Orientation.lean#L24-L33
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Orientation.lean#L24-L33

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

theorem Stanley.wellFounded_iff_no_cycle [Finite V] (r : V → V → Prop) :
    WellFounded r ↔ ∀ v, ¬ Relation.TransGen r v v := by sorry
