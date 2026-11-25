-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_finrank_obj_eq_of_iso
-- name    : PretorsionImageClosed.LinearQuiver.finrank_obj_eq_of_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:07:09.862542+00:00
-- url     : https://prove2.me/theorems/529c94fb-86ea-4219-89a5-be2ccc79c0c6
-- title:
--   Linear Quiver: finrank obj eq of iso
-- statement:
--   The Linear Quiver construction uses the finrank obj eq of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L118-L120
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L118-L120

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.finrank_obj_eq_of_iso {X Y : Statement.LinRep k n} (e : X ≅ Y) (i : Fin n) :
    Module.finrank k (X.obj i) = Module.finrank k (Y.obj i) := by sorry
