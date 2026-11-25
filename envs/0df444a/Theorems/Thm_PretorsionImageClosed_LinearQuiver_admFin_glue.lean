-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_admFin_glue
-- name    : PretorsionImageClosed.LinearQuiver.admFin_glue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:20:30.540416+00:00
-- url     : https://prove2.me/theorems/d0954add-2ad3-5f39-82f4-8a1b8d6ad370
-- title:
--   Linear Quiver: adm Fin glue
-- statement:
--   Lemma 8.4(2): the admissible starts `< n + 1` of `D_J`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L284-L328
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L284-L328

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.admFin_glue {D : IntervalFamily n} {J : Finset (Fin (n + 1))} (hJ : J ⊆ adm D) :
    admFin (D.glue J) = J ∪ (adm D).filter (fun c => ∀ a ∈ J, c ≤ a) := by sorry
