-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_indCard_subcategory_family
-- name    : PretorsionImageClosed.LinearQuiver.indCard_subcategory_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:04:42.093771+00:00
-- url     : https://prove2.me/theorems/97cff19c-b8ae-50c2-b8b8-51fd62a0d9aa
-- title:
--   Linear Quiver: ind Card subcategory family
-- statement:
--   The Linear Quiver construction uses the ind Card subcategory family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalFamilies.lean#L154-L163
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalFamilies.lean#L154-L163

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.indCard_subcategory_family (D : IntervalFamily n) :
    indCard (D.subcategory (k := k)).prop = D.D.card := by sorry
