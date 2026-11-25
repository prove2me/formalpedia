-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_interval_of_mono
-- name    : PretorsionImageClosed.LinearQuiver.exists_interval_of_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:10:56.049159+00:00
-- url     : https://prove2.me/theorems/adade1f3-39ee-482e-ba4d-8d308489b297
-- title:
--   Linear Quiver: exists interval of mono
-- statement:
--   An interval subobject of an object of `C` is a subobject of an interval of `C`
--   with the same right endpoint and a smaller left endpoint.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L96-L117
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L96-L117

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.exists_interval_of_mono (C : Subcategory (Statement.LinRep k n)) {a b : Fin n} (hab : a ≤ b)
    {Y : Statement.LinRep k n} (hY : C.prop Y) (i : interval k a b ⟶ Y) [Mono i] :
    ∃ c : Fin n, c ≤ a ∧ C.prop (interval k c b) := by sorry
